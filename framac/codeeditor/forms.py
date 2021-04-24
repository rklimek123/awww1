from django import forms
from . import models


class AddFileForm(forms.Form):
    file_name = forms.CharField(label='File', max_length=200)
    description = forms.CharField(label='Description', max_length=3000, required=False)
    directory = forms.ModelChoiceField(label='Directory',
                                       queryset=models.Directory.objects.all(),
                                       empty_label="~",
                                       required=False)
