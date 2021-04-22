from django.db import models
from django.contrib.auth.hashers import make_password
from django.contrib.auth.password_validation import validate_password


class User(models.Model):
    name = models.TextField(max_length=200)
    login = models.TextField(max_length=200)
    password = models.TextField(max_length=78)
    creation_date = models.DateTimeField(auto_now_add=True)
    modify_date = models.DateTimeField(auto_now=True)
    available = models.BooleanField(default=True)

    def __str__(self):
        return self.name

    def save(self):
        validate_password(self.password)
        self.password = make_password(self.password)
        super().save()


class Directory(models.Model):
    name = models.CharField(max_length=200)
    description = models.CharField(max_length=3000, blank=True, null=True)
    owner = models.ForeignKey(User, on_delete=models.SET_NULL, null=True)

    parent = models.ForeignKey('self', on_delete=models.CASCADE, blank=True, null=True)

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
    owner = models.ForeignKey(User, on_delete=models.SET_NULL, null=True)

    content = models.TextField(max_length=1000000, blank=True)
    directory = models.ForeignKey(Directory, on_delete=models.CASCADE, blank=True, null=True)

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
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    creation_date = models.DateTimeField(auto_now_add=True)
    modify_date = models.DateTimeField(auto_now=True)
    available = models.BooleanField(default=True)

    class Meta:
        verbose_name_plural = "Section statuses' data"


class FileSection(models.Model):
    name = models.CharField(max_length=200, blank=True, null=True)
    description = models.CharField(max_length=1000, blank=True, null=True)
    section_category = models.ForeignKey(SectionCategory, on_delete=models.CASCADE)
    section_status = models.ForeignKey(SectionStatus, on_delete=models.SET_NULL, null=True)
    section_status_data = models.ForeignKey(SectionStatusData, on_delete=models.SET_NULL, null=True)

    content = models.FileField(max_length=2000)
    is_subsection = models.BooleanField(default=False)
    parent_section = models.ForeignKey('self', on_delete=models.CASCADE, limit_choices_to={'is_subsection': True})
    parent_file = models.ForeignKey(File, on_delete=models.CASCADE, limit_choices_to={'is_subsection': False})

    creation_date = models.DateTimeField(auto_now_add=True)
    modify_date = models.DateTimeField(auto_now=True)
    available = models.BooleanField(default=True)
