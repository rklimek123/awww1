from django.core.files.uploadedfile import SimpleUploadedFile
from django.test import TestCase

from codeeditor.forms import *
from codeeditor.models import *


class AddSectionFormTestCase(TestCase):
    def setUp(self):
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
            name='test_file.c',
            description='Test file',
            content=f,
            directory=None,
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
            content='Proved successfully',
            user=None
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

    def test_add_section_to_file_ok(self):
        file = File.objects.get(name='test_file.c')

        form = AddSectionForm({
            'section_status_content': "content of section",
            'is_subsection': False,
            'parent_section': None,
            'parent_file': file,
            'description': 'section description',
            'begin': 22,
            'end': 34,
            'section_category': SectionCategory.objects.get(name='invariant'),
            'section_status': SectionStatus.objects.get(name='OK')
        })

        self.assertTrue(form.is_valid())

    def test_add_section_to_section_ok(self):
        section = FileSection.objects.get(name='invariant outer loop')

        form = AddSectionForm({
                'section_status_content': "content of section",
                'is_subsection': True,
                'parent_section': section,
                'parent_file': None,
                'description': 'section description',
                'begin': 22,
                'end': 34,
                'section_category': SectionCategory.objects.get(name='invariant'),
                'section_status': SectionStatus.objects.get(name='OK')
        })

        self.assertTrue(form.is_valid())

    def test_add_section_double_parents(self):
        section = FileSection.objects.get(name='invariant outer loop')
        file = File.objects.get(name='test_file.c')

        form = AddSectionForm({
                'section_status_content': "content of section",
                'is_subsection': False,
                'parent_section': section,
                'parent_file': file,
                'description': 'section description',
                'begin': 22,
                'end': 34,
                'section_category': SectionCategory.objects.get(name='invariant'),
                'section_status': SectionStatus.objects.get(name='OK')
            })

        self.assertFalse(form.is_valid())

    def test_add_section_to_section_wrong_mark(self):
        section = FileSection.objects.get(name='invariant outer loop')

        form = AddSectionForm({
                'section_status_content': "content of section",
                'is_subsection': False,
                'parent_section': section,
                'parent_file': None,
                'description': 'section description',
                'begin': 22,
                'end': 34,
                'section_category': SectionCategory.objects.get(name='invariant'),
                'section_status': SectionStatus.objects.get(name='OK')
            })

        self.assertFalse(form.is_valid())

    def test_add_section_to_file_wrong_mark(self):
        file = File.objects.get(name='test_file.c')

        form = AddSectionForm({
            'section_status_content': "content of section",
            'is_subsection': True,
            'parent_section': None,
            'parent_file': file,
            'description': 'section description',
            'begin': 22,
            'end': 34,
            'section_category': SectionCategory.objects.get(name='invariant'),
            'section_status': SectionStatus.objects.get(name='OK')
        })

        self.assertFalse(form.is_valid())

    def test_add_section_to_section_not_contained(self):
        section = FileSection.objects.get(name='invariant outer loop')

        form = AddSectionForm({
               'section_status_content': "content of section",
               'is_subsection': True,
               'parent_section': section,
               'parent_file': None,
               'description': 'section description',
               'begin': 2,
               'end': 30,
               'section_category': SectionCategory.objects.get(name='invariant'),
               'section_status': SectionStatus.objects.get(name='OK')
        })

        self.assertFalse(form.is_valid())

    def test_add_section_negative_line(self):
        file = File.objects.get(name='test_file.c')

        form = AddSectionForm({
            'section_status_content': "content of section",
            'is_subsection': False,
            'parent_section': None,
            'parent_file': file,
            'description': 'section description',
            'begin': -22,
            'end': 34,
            'section_category': SectionCategory.objects.get(name='invariant'),
            'section_status': SectionStatus.objects.get(name='OK')
        })

        self.assertFalse(form.is_valid())

    def test_add_section_begin_greater_than_end(self):
        file = File.objects.get(name='test_file.c')

        form = AddSectionForm({
            'section_status_content': "content of section",
            'is_subsection': False,
            'parent_section': None,
            'parent_file': file,
            'description': 'section description',
            'begin': 34,
            'end': 22,
            'section_category': SectionCategory.objects.get(name='invariant'),
            'section_status': SectionStatus.objects.get(name='OK')
        })

        self.assertFalse(form.is_valid())
