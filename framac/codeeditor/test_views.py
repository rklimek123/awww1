from django.core.files.uploadedfile import SimpleUploadedFile
from django.test import TestCase

from .forms import *
from .models import *
from .views import *


class CodeEditorContextTestCase(TestCase):
    def setUp(self):
        user = User.objects.create(username="userTEST", password="rk418291!students")

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

        file_section = FileSection.objects.create(
            name='invariant outer loop',
            description='Outer loop invariant testing the correctness of this certain invariant',
            section_category=category_invariant,
            section_status=status_ok,
            section_status_data=status_data_ok,
            begin=15,
            end=34,
            parent_file=file
        )

        file_section_sub = FileSection.objects.create(
            name='invariant inner loop',
            description='Inner loop invariant testing the correctness of this certain invariant',
            section_category=category_invariant,
            section_status=status_ok,
            section_status_data=status_data_ok,
            begin=22,
            end=32,
            is_subsection=True,
            parent_section=file_section
        )

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
                                 ))

        self.assertQuerysetEqual(ctx['inroot_files'],
                                 File.objects.filter(
                                     directory=None,
                                     available=True
                                 ))

        for direct, in_dirs in ctx['in_dirs'].items():
            self.assertQuerysetEqual(
                Directory.objects.filter(parent=direct, available=True),
                in_dirs
            )

            for dire in in_dirs:
                self.assertTrue(dire.parent == direct)

        for direct, in_files in ctx['in_files'].items():
            self.assertQuerysetEqual(
                File.objects.filter(directory=direct, available=True),
                in_files
            )

            for file in in_files:
                self.assertTrue(file.parent == direct)

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
                                 ))

        self.assertQuerysetEqual(ctx['inroot_files'],
                                 File.objects.filter(
                                     directory=None,
                                     available=True
                                 ))

        for direct, in_dirs in ctx['in_dirs'].items():
            self.assertQuerysetEqual(
                Directory.objects.filter(parent=direct, available=True),
                in_dirs
            )

            for dire in in_dirs:
                self.assertTrue(dire.parent == direct)

        for direct, in_files in ctx['in_files'].items():
            self.assertQuerysetEqual(
                File.objects.filter(directory=direct, available=True),
                in_files
            )

            for file in in_files:
                self.assertTrue(file.parent == direct)

        self.assertEqual(ctx['selected_file'], file)
        self.assertEqual(ctx['filelines'], file.get_content())
        self.assertEqual(ctx['tab'], 2)
        self.assertNotIn(ctx['result_tab'], ['', None])
        self.assertEqual(ctx['provers_form'], forms.ChooseProverForm())
        self.assertEqual(ctx['vcs_form'], forms.ChooseVcForm())

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
                                 ))

        self.assertQuerysetEqual(ctx['inroot_files'],
                                 File.objects.filter(
                                     directory=None,
                                     available=True
                                 ))

        for direct, in_dirs in ctx['in_dirs'].items():
            self.assertQuerysetEqual(
                Directory.objects.filter(parent=direct, available=True),
                in_dirs
            )

            for dire in in_dirs:
                self.assertTrue(dire.parent == direct)

        for direct, in_files in ctx['in_files'].items():
            self.assertQuerysetEqual(
                File.objects.filter(directory=direct, available=True),
                in_files
            )

            for file in in_files:
                self.assertTrue(file.parent == direct)

        self.assertEqual(ctx['selected_file'], file)
        self.assertEqual(ctx['filelines'], file.get_content())

        frama_call = 'frama-c -wp -wp-print upload/' + file.content.name
        frama_result = subprocess.getstatusoutput(frama_call)
        self.assertEqual(frama_result[0], 0)

        frama_out = parse_frama_output(frama_result[1], file)
        self.assertEqual(ctx['first_section'], frama_out[0])
        self.assertEqual(ctx['sections'], frama_out[1])

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
                                 ))

        self.assertQuerysetEqual(ctx['inroot_files'],
                                 File.objects.filter(
                                     directory=None,
                                     available=True
                                 ))

        for direct, in_dirs in ctx['in_dirs'].items():
            self.assertQuerysetEqual(
                Directory.objects.filter(parent=direct, available=True),
                in_dirs
            )

            for dire in in_dirs:
                self.assertTrue(dire.parent == direct)

        for direct, in_files in ctx['in_files'].items():
            self.assertQuerysetEqual(
                File.objects.filter(directory=direct, available=True),
                in_files
            )

            for file in in_files:
                self.assertTrue(file.parent == direct)

        self.assertEqual(ctx['selected_file'], file)
        self.assertEqual(ctx['filelines'], file.get_content())
        frama_call = 'frama-c -wp -wp-prover z3-ce -wp-prop="-@invariant" upload/' + file.content.name
        frama_result = subprocess.getstatusoutput(frama_call)
        self.assertEqual(frama_result[0], 0)

        frama_out = parse_frama_output(frama_result[1], file)
        self.assertEqual(ctx['first_section'], frama_out[0])
        self.assertEqual(ctx['sections'], frama_out[1])

    def test_add_file(self):
        self.authorize()

        response = self.client.get(reverse('addfile'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertTrue(ctx['form'] is AddFileForm)
        self.assertEqual(ctx['action'], reverse('addfile'))

    def test_add_section(self):
        self.authorize()

        response = self.client.get(reverse('addsection'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertTrue(ctx['form'] is AddSectionForm)
        self.assertEqual(ctx['action'], reverse('addsection'))

    def test_add_directory(self):
        self.authorize()

        response = self.client.get(reverse('adddirectory'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertTrue(ctx['form'] is AddDirectoryForm)
        self.assertEqual(ctx['action'], reverse('adddirectory'))

    def test_delete_file(self):
        self.authorize()

        response = self.client.get(reverse('deletefile'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertTrue(ctx['form'] is DeleteFileForm)
        self.assertEqual(ctx['action'], reverse('deletefile'))

    def test_delete_directory(self):
        self.authorize()

        response = self.client.get(reverse('deletedirectory'))
        self.assertEqual(response.status_code, 200)
        ctx = response.context
        self.assertTrue(ctx['form'] is DeleteDirectoryForm)
        self.assertEqual(ctx['action'], reverse('deletedirectory'))


# class CodeEditorPostTestCase(TestCase):
# todo


# class CodeEditorFramaTestCase(TestCase):
# todo
