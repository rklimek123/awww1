from django.db import models
from django.contrib.auth.models import User

class Directory(models.Model):
    name = models.CharField(max_length=200)
    description = models.CharField(max_length=3000, blank=True, null=True)
    owner = models.ForeignKey(User,
                              on_delete=models.SET_NULL,
                              null=True,
                              limit_choices_to={'available': True})

    parent = models.ForeignKey('self',
                               on_delete=models.CASCADE,
                               blank=True,
                               null=True,
                               limit_choices_to={'available': True})

    creation_date = models.DateTimeField(auto_now_add=True)
    modify_date = models.DateTimeField(auto_now=True)
    available = models.BooleanField(default=True)

    def __str__(self):
        return self.name

    class Meta:
        verbose_name_plural = "Directories"


class File(models.Model):
    name = models.CharField(max_length=200)
    description = models.CharField(max_length=3000, blank=True, null=True)
    owner = models.ForeignKey(User,
                              on_delete=models.CASCADE,
                              null=True,
                              limit_choices_to={'available': True})

    directory = models.ForeignKey(Directory,
                                  on_delete=models.CASCADE,
                                  blank=True,
                                  null=True,
                                  limit_choices_to={'available': True})

    creation_date = models.DateTimeField(auto_now_add=True)
    modify_date = models.DateTimeField(auto_now=True)
    available = models.BooleanField(default=True)

    def __str__(self):
        return self.name


class SectionCategory(models.Model):
    name = models.CharField(max_length=500)
    creation_date = models.DateTimeField(auto_now_add=True)
    modify_date = models.DateTimeField(auto_now=True)
    available = models.BooleanField(default=True)

    def __str__(self):
        return '<' + self.name + '>'

    class Meta:
        verbose_name_plural = "Section categories"


class SectionStatus(models.Model):
    name = models.CharField(max_length=500)
    creation_date = models.DateTimeField(auto_now_add=True)
    modify_date = models.DateTimeField(auto_now=True)
    available = models.BooleanField(default=True)

    def __str__(self):
        return '[' + self.name + ']'

    class Meta:
        verbose_name_plural = "Section statuses"


class SectionStatusData(models.Model):
    content = models.TextField(max_length=5000)
    user = models.ForeignKey(User, on_delete=models.CASCADE, limit_choices_to={'available': True})
    creation_date = models.DateTimeField(auto_now_add=True)
    modify_date = models.DateTimeField(auto_now=True)
    available = models.BooleanField(default=True)

    class Meta:
        verbose_name_plural = "Section statuses' data"


class FileSection(models.Model):
    name = models.CharField(max_length=200, blank=True, null=True)
    description = models.CharField(max_length=1000, blank=True, null=True)
    section_category = models.ForeignKey(SectionCategory,
                                         on_delete=models.CASCADE,
                                         limit_choices_to={'available': True})
    section_status = models.ForeignKey(SectionStatus,
                                       on_delete=models.SET_NULL,
                                       null=True,
                                       limit_choices_to={'available': True})
    section_status_data = models.ForeignKey(SectionStatusData,
                                            on_delete=models.SET_NULL,
                                            null=True,
                                            limit_choices_to={'available': True})

    content = models.CharField(max_length=1000000)
    is_subsection = models.BooleanField(default=False)
    parent_section = models.ForeignKey('self',
                                       on_delete=models.CASCADE,
                                       blank=True,
                                       null=True,
                                       limit_choices_to={'available': True})
    parent_file = models.ForeignKey(File,
                                    on_delete=models.CASCADE,
                                    blank=True,
                                    null=True,
                                    limit_choices_to={'available': True})

    creation_date = models.DateTimeField(auto_now_add=True)
    modify_date = models.DateTimeField(auto_now=True)
    available = models.BooleanField(default=True)

    def get_file(self):
        obj = self
        while obj.is_subsection:
            obj = obj.parent_section
        return obj.parent_file

    def save(self, *args, **kwargs):
        if self.parent_file is not None and self.parent_section is not None:
            raise Exception('Section has both file and section as parents.')

        if self.is_subsection:
            if self.parent_section is None:
                raise Exception("Subsection doesn't have a section parent.")
        else:
            if self.parent_file is None:
                raise Exception("Main Section doesn't have a file parent.")
        super().save(args, kwargs)

    def get_raw_name(self):
        if self.name is not None:
            return self.name
        else:
            return str(self.section_category)

    def __str__(self):
        section = self
        result = self.get_raw_name() + " ))"

        while section.is_subsection:
            section = section.parent_section
            result = section.get_raw_name() + "-->" + result
        result = "(( " + str(section.parent_file) + ":" + result
        return result
