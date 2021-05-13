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
        return self.get_breadcrumbs()

    def get_breadcrumbs(self):
        string = self.name
        directory = "~/"
        if self.parent is not None:
            directory = self.parent.get_breadcrumbs()
        return directory + string + "/"

    def mark_inavailable(self):
        files = File.objects.filter(directory=self, available=True)
        for file in files:
            file.mark_inavailable()
        subdirectories = Directory.objects.filter(parent=self, available=True)
        for dire in subdirectories:
            dire.mark_inavailable()
        self.available = False
        self.save()

    class Meta:
        verbose_name_plural = "Directories"


class Prover(models.Model):
    name = models.TextField(max_length=50)
    arg = models.TextField(max_length=50)
    creation_date = models.DateTimeField(auto_now_add=True)
    modify_date = models.DateTimeField(auto_now=True)
    available = models.BooleanField(default=True)

    def __str__(self):
        return self.name


class File(models.Model):
    name = models.CharField(max_length=200)
    description = models.CharField(max_length=3000, blank=True, null=True)
    owner = models.ForeignKey(User,
                              on_delete=models.CASCADE,
                              null=True,
                              limit_choices_to={'available': True})

    content = models.FileField()

    directory = models.ForeignKey(Directory,
                                  on_delete=models.CASCADE,
                                  blank=True,
                                  null=True,
                                  limit_choices_to={'available': True})

    creation_date = models.DateTimeField(auto_now_add=True)
    modify_date = models.DateTimeField(auto_now=True)
    available = models.BooleanField(default=True)
    prover = models.ForeignKey(Prover,
                               on_delete=models.SET_NULL,
                               blank=True,
                               null=True,
                               limit_choices_to={'available': True})
    rte = models.BooleanField(default=False)
    vcs = models.CharField(max_length=1000, blank=True, null=True)

    def __str__(self):
        string = self.name
        directory = "~/"
        if self.directory is not None:
            directory = self.directory.get_breadcrumbs()
        return directory + string

    def mark_inavailable(self):
        sections = FileSection.objects.filter(parent_file=self, available=True)
        for section in sections:
            section.mark_inavailable()
        self.available = False
        super().save()

    def get_content(self):
        file = self.content
        file.open("r")
        lines = file.readlines()
        file.close()
        result = []
        for line in lines:
            result.append(line[:len(line) - 1])  # .readlines() puts a '\n' at the end of each line
        return result


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
    section_status_data = models.OneToOneField(SectionStatusData,
                                               on_delete=models.SET_NULL,
                                               null=True,
                                               limit_choices_to={'available': True})

    begin = models.IntegerField()
    end = models.IntegerField()
    is_subsection = models.BooleanField(default=False)
    parent_section = models.ForeignKey('self',
                                       on_delete=models.CASCADE,
                                       blank=True,
                                       null=True,
                                       limit_choices_to={'available': True})
    parent_file = models.ForeignKey(File,
                                    on_delete=models.CASCADE,
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
        if self.is_subsection:
            if self.parent_section is None:
                raise Exception("Subsection doesn't have a section parent.")
        else:
            if self.parent_section is not None:
                raise Exception("A section, which is not a subsection, has a section parent.")

        super().save(args, kwargs)

    def delete(self):
        status_data = self.section_status_data
        status_data.delete()
        super().delete()

    def mark_inavailable(self):
        subsections = FileSection.objects.filter(parent_section=self, available=True)
        self.available = False
        self.save()

    def get_raw_name(self):
        if self.name is not None:
            return self.name
        else:
            return str(self.section_category)

    def __str__(self):
        section = self
        result = self.get_raw_name() + " )"

        while section.is_subsection:
            section = section.parent_section
            result = section.get_raw_name() + "-->" + result
        result = "( " + str(section.parent_file) + ":" + result
        return result

    def get_hierarchy_name(self):
        section = self
        result = self.get_raw_name()
        while section.is_subsection:
            section = section.parent_section
            result = section.get_raw_name() + "-->" + result
        return result
