from django.core.files.uploadedfile import SimpleUploadedFile
from django.test import TestCase

from codeeditor.forms import *
from codeeditor.models import *
from codeeditor.views import *


def global_setUp():
    user = User.objects.create(username="userTEST")
    user.set_password("rk418291!students")
    user.save()

    dir_outer = Directory.objects.create(
        name='outer',
        description='Test directory',
        parent=None
    )

    dir_inner = Directory.objects.create(
        name='inner',
        description='Test directory 2',
        parent=dir_outer
    )

    prover = Prover.objects.create(
        name='Z3',
        arg='z3-ce'
    )

    f = SimpleUploadedFile("test_frama.c", b"""
            #pragma JessieIntegerModel(math)

            /*@ predicate Sorted{L}(int *a, integer l, integer h) =
              @   \\forall integer i,j; l <= i <= j < h ==> a[i] <= a[j] ;
              @*/

            /*@ requires \\valid_range(t,0,n-1);
              @ ensures Sorted(t,0,n-1);
              @*/
            void insert_sort(int t[], int n) {
              int i,j;
              int mv;
              if (n <= 1) return;
              /*@ loop invariant 0 <= i <= n;
                @ loop invariant Sorted(t,0,i);
                @ loop variant n-i;
                @*/
              for (i=1; i<n; i++) {
                // assuming t[0..i-1] is sorted, insert t[i] at the right place
                mv = t[i]; 
                /*@ loop invariant 0 <= j <= i;
                  @ loop invariant j == i ==> Sorted(t,0,i);
                  @ loop invariant j < i ==> Sorted(t,0,i+1);
                  @ loop invariant \\forall integer k; j <= k < i ==> t[k] > mv;
                  @ loop variant j;
                  @*/
                // look for the right index j to put t[i]
                for (j=i; j > 0; j--) {
                  if (t[j-1] <= mv) break;
                  t[j] = t[j-1];
                }
                t[j] = mv;
              }
            }


            /*
            Local Variables:
            compile-command: "frama-c -jessie insertion_sort.c"
            End:
            */
            """)

    file = File.objects.create(
        pk=1,
        name='test_file.c',
        description='Test file',
        content=f,
        directory=dir_outer,
        prover=None,
        vcs=''
    )

    category_invariant = SectionCategory.objects.create(
        name='invariant'
    )

    status_ok = SectionStatus.objects.create(
        name='OK'
    )

    status_data_ok = SectionStatusData.objects.create(
        content='Proved successfully'
    )

    status_data_sub_ok = SectionStatusData.objects.create(
        content='Proved successfully sub'
    )

    file_section = FileSection(
        name='invariant outer loop',
        description='Outer loop invariant testing the correctness of this certain invariant',
        section_category=category_invariant,
        section_status=status_ok,
        section_status_data=status_data_ok,
        begin=15,
        end=34,
        parent_file=file
    )
    file_section.save()

    file_section_sub = FileSection(
        name='invariant inner loop',
        description='Inner loop invariant testing the correctness of this certain invariant',
        section_category=category_invariant,
        section_status=status_ok,
        section_status_data=status_data_sub_ok,
        begin=22,
        end=32,
        is_subsection=True,
        parent_section=file_section,
        parent_file=file
    )
    file_section_sub.save()

class CodeEditorContextTestCase(TestCase):
    def setUp(self):
        global_setUp()

    def authorize(self):
        response = self.client.post(reverse('login'), {'username': 'userTEST', 'password': 'rk418291!students'})

    def test_view_blank(self):
        self.authorize()

        response = self.client.get(reverse('index'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context

        self.assertQuerysetEqual(ctx['inroot_dirs'],
                                 Directory.objects.filter(
                                     parent=None,
                                     available=True
                                 ),
                                 transform=lambda x: x)

        self.assertQuerysetEqual(ctx['inroot_files'],
                                 File.objects.filter(
                                     directory=None,
                                     available=True
                                 ),
                                 transform=lambda x: x)

        for direct, in_dirs in ctx['in_dirs'].items():
            self.assertQuerysetEqual(
                Directory.objects.filter(parent=direct, available=True),
                in_dirs,
                transform=lambda x: x
            )

            for dire in in_dirs:
                self.assertTrue(dire.parent == direct)

        for direct, in_files in ctx['in_files'].items():
            self.assertQuerysetEqual(
                File.objects.filter(directory=direct, available=True),
                in_files,
                transform=lambda x: x
            )

            for file in in_files:
                self.assertTrue(file.directory == direct)

    def test_pre_verification(self):
        self.authorize()
        file = File.objects.get(name='test_file.c')

        response = self.client.get(reverse('noframa', kwargs={'id': file.pk}) + '?tab=2')
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertQuerysetEqual(ctx['inroot_dirs'],
                                 Directory.objects.filter(
                                     parent=None,
                                     available=True
                                 ),
                                 transform=lambda x: x)

        self.assertQuerysetEqual(ctx['inroot_files'],
                                 File.objects.filter(
                                     directory=None,
                                     available=True
                                 ),
                                 transform=lambda x: x)

        for direct, in_dirs in ctx['in_dirs'].items():
            self.assertQuerysetEqual(
                Directory.objects.filter(parent=direct, available=True),
                in_dirs,
                transform=lambda x: x
            )

            for dire in in_dirs:
                self.assertTrue(dire.parent == direct)

        for direct, in_files in ctx['in_files'].items():
            self.assertQuerysetEqual(
                File.objects.filter(directory=direct, available=True),
                in_files,
                transform=lambda x: x
            )

            for file in in_files:
                self.assertTrue(file.directory == direct)

        self.assertEqual(ctx['selected_file'], file)
        self.assertEqual(ctx['filelines'], file.get_content())
        self.assertEqual(ctx['tab'], 2)
        self.assertNotIn(ctx['result_tab'], ['', None])
        self.assertIsInstance(ctx['provers_form'], forms.ChooseProverForm)
        self.assertIsInstance(ctx['vcs_form'], forms.ChooseVcForm)

    def test_view_selected(self):
        self.authorize()
        file = File.objects.get(name='test_file.c')

        response = self.client.get(reverse('main', kwargs={'id': file.pk}))
        self.assertEqual(response.status_code, 200)

        ctx = response.context
        self.assertQuerysetEqual(ctx['inroot_dirs'],
                                 Directory.objects.filter(
                                     parent=None,
                                     available=True
                                 ),
                                 transform=lambda x: x)

        self.assertQuerysetEqual(ctx['inroot_files'],
                                 File.objects.filter(
                                     directory=None,
                                     available=True
                                 ),
                                 transform=lambda x: x)

        for direct, in_dirs in ctx['in_dirs'].items():
            self.assertQuerysetEqual(
                Directory.objects.filter(parent=direct, available=True),
                in_dirs,
                transform=lambda x: x
            )

            for dire in in_dirs:
                self.assertTrue(dire.parent == direct)

        for direct, in_files in ctx['in_files'].items():
            self.assertQuerysetEqual(
                File.objects.filter(directory=direct, available=True),
                in_files,
                transform=lambda x: x
            )

            for file in in_files:
                self.assertTrue(file.directory == direct)

        self.assertEqual(ctx['selected_file'], file)
        self.assertEqual(ctx['filelines'], file.get_content())

        frama_call = 'frama-c -wp -wp-print upload/' + file.content.name
        frama_result = subprocess.getstatusoutput(frama_call)
        self.assertEqual(frama_result[0], 0)

        frama_out = parse_frama_output(frama_result[1], file)

        self.assertEqual(ctx['first_section'][0], frama_out[0][0])
        self.assertEqual(ctx['sections'][0], frama_out[1][0])

    def test_view_selected_custom(self):
        self.authorize()
        file = File.objects.get(name='test_file.c')

        response = self.client.get(reverse('main', kwargs={'id': file.pk}) + "?custom=1")
        self.assertEqual(response.status_code, 200)

        ctx = response.context
        self.assertQuerysetEqual(ctx['inroot_dirs'],
                                 Directory.objects.filter(
                                     parent=None,
                                     available=True
                                 ),
                                 transform=lambda x: x)

        self.assertQuerysetEqual(ctx['inroot_files'],
                                 File.objects.filter(
                                     directory=None,
                                     available=True
                                 ),
                                 transform=lambda x: x)

        for direct, in_dirs in ctx['in_dirs'].items():
            self.assertQuerysetEqual(
                Directory.objects.filter(parent=direct, available=True),
                in_dirs,
                transform=lambda x: x
            )

            for dire in in_dirs:
                self.assertTrue(dire.parent == direct)

        for direct, in_files in ctx['in_files'].items():
            self.assertQuerysetEqual(
                File.objects.filter(directory=direct, available=True),
                in_files,
                transform=lambda x: x
            )

            for file in in_files:
                self.assertTrue(file.directory == direct)

        self.assertEqual(ctx['selected_file'], file)
        self.assertEqual(ctx['filelines'], file.get_content())
        frama_call = 'frama-c -wp -wp-prover z3-ce -wp-prop="-@invariant" upload/' + file.content.name
        frama_result = subprocess.getstatusoutput(frama_call)
        self.assertEqual(frama_result[0], 0)

        frama_out = parse_frama_output(frama_result[1], file)
        self.assertEqual(ctx['first_section'][0], frama_out[0][0])

        try:
            print(ctx['sections'][0])
            self.assertTrue(False)
        except IndexError:
            self.assertTrue(True)

        try:
            print(frama_out[1][0])
            self.assertTrue(False)
        except IndexError:
            self.assertTrue(True)

    def test_add_file(self):
        self.authorize()

        response = self.client.get(reverse('addfile'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertIsInstance(ctx['form'], AddFileForm)
        self.assertEqual(ctx['action'], reverse('addfile'))

    def test_add_section(self):
        self.authorize()

        response = self.client.get(reverse('addsection'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertIsInstance(ctx['form'], AddSectionForm)
        self.assertEqual(ctx['action'], reverse('addsection'))

    def test_add_directory(self):
        self.authorize()

        response = self.client.get(reverse('adddirectory'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertIsInstance(ctx['form'], AddDirectoryForm)
        self.assertEqual(ctx['action'], reverse('adddirectory'))

    def test_delete_file(self):
        self.authorize()

        response = self.client.get(reverse('deletefile'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertIsInstance(ctx['form'], DeleteFileForm)
        self.assertEqual(ctx['action'], reverse('deletefile'))

    def test_delete_directory(self):
        self.authorize()

        response = self.client.get(reverse('deletedirectory'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertIsInstance(ctx['form'], DeleteDirectoryForm)
        self.assertEqual(ctx['action'], reverse('deletedirectory'))


class CodeEditorPostTestCase(TestCase):
    def setUp(self):
        global_setUp()

    def authorize(self):
        response = self.client.post(reverse('login'), {'username': 'userTEST', 'password': 'rk418291!students'})

    def test_pre_verification_unauth(self):
        file = File.objects.get(name='test_file.c')
        prover = Prover.objects.get(name='Z3')

        response = self.client.post(reverse('noframa', kwargs={'id': file.pk}), {'prover': prover.pk})
        self.assertEqual(response.status_code, 302)

    def test_pre_verification_prover(self):
        self.authorize()
        file = File.objects.get(name='test_file.c')
        self.assertIsNone(file.prover)

        prover = Prover.objects.get(name='Z3')

        response = self.client.post(reverse('noframa', kwargs={'id': file.pk}), {'prover': prover.pk})
        self.assertEqual(response.status_code, 200)

        file = File.objects.get(name='test_file.c')
        self.assertEqual(file.prover, prover)

    def test_pre_verification_vcs(self):
        self.authorize()
        file = File.objects.get(name='test_file.c')

        if file.vcs is None:
            self.assertIsNone(file.vcs)
        else:
            self.assertEqual(file.vcs, '')

        vc = '--invariant'

        response = self.client.post(reverse('noframa', kwargs={'id': file.pk}), {'vc': vc})
        self.assertEqual(response.status_code, 200)

        file = File.objects.get(name='test_file.c')
        self.assertEqual(file.vcs, vc)

    def test_pre_verification_rte(self):
        self.authorize()
        file = File.objects.get(name='test_file.c')

        self.assertFalse(file.rte)

        response = self.client.post(reverse('noframa', kwargs={'id': file.pk}), {'vc': '', 'rte': ''})
        self.assertEqual(response.status_code, 200)

        file = File.objects.get(name='test_file.c')
        self.assertTrue(file.rte)

    def test_add_section_unauth(self):
        file = File.objects.get(name='test_file.c')
        section_category = SectionCategory.objects.get(name='invariant')
        section_status = SectionStatus.objects.get(name='OK')

        response = self.client.post(reverse('addsection'),
                                    {'name': "test section",
                                     'section_status_content': "content of section",
                                     'is_subsection': False,
                                     'parent_file': file.pk,
                                     'description': 'section description',
                                     'begin': 22,
                                     'end': 34,
                                     'section_category': section_category.pk,
                                     'section_status': section_status.pk
                                     })
        self.assertEqual(response.status_code, 302)

    def test_add_section(self):
        self.authorize()

        file = File.objects.get(name='test_file.c')
        section_category = SectionCategory.objects.get(name='invariant')
        section_status = SectionStatus.objects.get(name='OK')

        response = self.client.post(reverse('addsection'),
                                    {'name': "test section",
                                     'section_status_content': "content of section",
                                     'is_subsection': False,
                                     'parent_file': file.pk,
                                     'description': 'section description',
                                     'begin': 22,
                                     'end': 34,
                                     'section_category': section_category.pk,
                                     'section_status': section_status.pk
                                     })
        self.assertEqual(response.status_code, 200)
        section = FileSection.objects.get(name='test section')
        self.assertIsNotNone(section)
        self.assertEqual(section.name, "test section")
        self.assertEqual(section.section_status_data.content, "content of section")
        self.assertFalse(section.is_subsection)
        self.assertIsNone(section.parent_section)
        self.assertEqual(section.parent_file, file)
        self.assertEqual(section.description, "section description")
        self.assertEqual(section.begin, 22)
        self.assertEqual(section.end, 34)
        self.assertEqual(section.section_category, section_category)
        self.assertEqual(section.section_status, section_status)

    def test_add_directory_unauth(self):
        response = self.client.post(reverse('adddirectory'),
                                    {'name': "testdir",
                                     'description': 'testdir description'
                                     })
        self.assertEqual(response.status_code, 302)
        self.assertEqual(response.url, '/login/')

    def test_add_directory(self):
        self.authorize()

        response = self.client.post(reverse('adddirectory'),
                                    {'name': "testdir",
                                     'description': 'testdir description'
                                     })
        self.assertEqual(response.status_code, 302)
        self.assertEqual(response.url, '/')

        direc = Directory.objects.get(name='testdir')
        self.assertIsNotNone(direc)
        self.assertEqual(direc.name, "testdir")
        self.assertEqual(direc.description, "testdir description")

"""
    def test_add_file(self):
        self.authorize()

        response = self.client.get(reverse('addfile'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertIsInstance(ctx['form'], AddFileForm)
        self.assertEqual(ctx['action'], reverse('addfile'))

    def test_delete_file(self):
        self.authorize()

        response = self.client.get(reverse('deletefile'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertIsInstance(ctx['form'], DeleteFileForm)
        self.assertEqual(ctx['action'], reverse('deletefile'))

    def test_delete_directory(self):
        self.authorize()

        response = self.client.get(reverse('deletedirectory'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertIsInstance(ctx['form'], DeleteDirectoryForm)
        self.assertEqual(ctx['action'], reverse('deletedirectory'))

"""
# class CodeEditorFramaTestCase(TestCase):
# todo
