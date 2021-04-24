from django import forms
from . import models


class AddFileForm(forms.ModelForm):
    directory = forms.ModelChoiceField(label='Directory',
                                       queryset=models.Directory.objects.filter(available=True),
                                       empty_label="~",
                                       required=False)

    class Meta:
        model = models.File
        fields = ['name', 'description', 'directory']


class AddSectionForm(forms.ModelForm):
    section_status_content = forms.CharField(label='Section status data', max_length=5000)

    def clean(self):
        super().clean()
        is_subsection = self.cleaned_data.get('is_subsection')
        psection = self.cleaned_data.get('parent_section')
        pfile = self.cleaned_data.get('parent_file')

        if pfile is not None and psection is not None:
            raise forms.ValidationError('Section must have only one parent.')

        if is_subsection:
            if psection is None:
                raise forms.ValidationError("Subsection must have a section parent.")
        else:
            if pfile is None:
                raise forms.ValidationError("Main Section must have a file parent.")

    class Meta:
        model = models.FileSection
        fields = ['is_subsection',
                  'parent_section',
                  'parent_file',
                  'name',
                  'description',
                  'content',
                  'section_category',
                  'section_status',
                  'section_status_content'
                  ]


class AddDirectoryForm(forms.ModelForm):
    parent = forms.ModelChoiceField(label='Parent directory',
                                    queryset=models.Directory.objects.filter(available=True),
                                    empty_label="~",
                                    required=False)

    class Meta:
        model = models.Directory
        fields = ['name', 'description', 'parent']


class DeleteFileForm(forms.Form):
    file = forms.ModelChoiceField(label='File to delete',
                                  queryset=models.File.objects.filter(available=True),
                                  empty_label='No file chosen')


class DeleteDirectoryForm(forms.Form):
    directory = forms.ModelChoiceField(label='Directory to delete',
                                       queryset=models.Directory.objects.filter(available=True),
                                       empty_label='No directory chosen')