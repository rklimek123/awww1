from django.test import TestCase
from .models import *


class FilesystemTestCase(TestCase):
    def setUp(self):
        user = User.objects.get_or_create(pk=1)

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

        f = open("test_frama.c", "w")
        f.write(
            r"""
#pragma JessieIntegerModel(math)

/*@ predicate Sorted{L}(int *a, integer l, integer h) =
  @   \forall integer i,j; l <= i <= j < h ==> a[i] <= a[j] ;
  @*/

/*@ requires \valid_range(t,0,n-1);
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
      @ loop invariant \forall integer k; j <= k < i ==> t[k] > mv;
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
            """
        )
        f.close()

        f_read = open("test_frama.c", "r")

        file = File.objects.create(
            name='test_file.c',
            description='Test file',
            content=f_read,
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


    def directory_breadcrumbs(self):
        dir_outer = Directory.objects.get(name='outer')
        dir_inner = Directory.objects.get(name='inner')

        self.assertEqual(dir_outer.get_breadcrumbs(), '~/outer/')
        self.assertEqual(dir_inner.get_breadcrumbs(), '~/outer/inner/')

        self.assertEqual(dir_outer.__str__(), '~/outer/')
        self.assertEqual(dir_inner.__str__(), '~/outer/inner/')

    # def directory_mark_inavailable(self):
    # todo

    # def directory_meta(self):
    # todo


    def prover_str(self):
        prover = Prover.objects.get(name='Z3')

        self.assertEqual(prover.__str__(), 'Z3')


    def file_str(self):
        file = File.objects.get(name='test_file.c')

        self.assertEqual(file.__str__(), '~/outer/test_file.c')

    # def file_mark_inavailable(self):
    # todo

    # def file_get_content(self):
    # todo


    def sectioncategory_str(self):
        section_category = SectionCategory.objects.get(name='invariant')

        self.assertEqual(section_category.__str__(), '<invariant>')

    # def sectioncategory_meta(self):
    # todo


    def sectionstatus_str(self):
        section_status = SectionStatus.objects.get(name='OK')

        self.assertEqual(section_status.__str__(), '[OK]')

    # def sectionstatus_meta(self):
    # todo


    def sectionstatusdata_meta(self):
        self.assertEqual(SectionStatusData._meta.verbose_name_plural, "Section statuses' data")


    def filesection_get_file(self):
        subsection = FileSection.objects.get(name='invariant inner loop')
        section = FileSection.objects.get(name='invariant outer loop')
        file = File.objects.get(name='test_file.c')

        self.assertEqual(section.get_file(), file)
        self.assertEqual(subsection.get_file(), file)

    # def filesection_mark_inavailable(self):
    # todo

    # def filesection_get_raw_name(self):
    # todo

    # def filesection_str(self):
    # todo

    # def filesection_get_hierarchy_name(self):
    # todo
