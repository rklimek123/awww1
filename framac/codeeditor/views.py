from django.contrib.auth.models import User
from django.http import HttpResponseRedirect
from django.views import View
from django.shortcuts import get_object_or_404, render

from . import models
from . import forms


class CodeEditorViewBlank(View):
    def get_context(self):
        ctx = {}
        ctx['inroot_dirs'] = models.Directory.objects.filter(parent=None).order_by('name')
        ctx['inroot_files'] = models.File.objects.filter(directory=None).order_by('name')
        ctx['in_dirs'] = {}
        ctx['in_files'] = {}
        for direct in models.Directory.objects.all():
            children_dirs = models.Directory.objects.filter(parent=direct).order_by('name')
            children_files = models.File.objects.filter(directory=direct).order_by('name')
            ctx['in_dirs'][direct] = children_dirs
            ctx['in_files'][direct] = children_files
        return ctx

    def get(self, request):
        return render(request, 'codeeditor/index.html', self.get_context())


class CodeEditorViewSelected(CodeEditorViewBlank):
    def get(self, request, *args, **kwargs):
        file_id = kwargs['id']
        ctx = self.get_context()
        ctx['selected_file'] = get_object_or_404(models.File, pk=file_id)
        # tu jakoś wyciąganie i format sekcji
        #content = ctx['selected_file'].content
        #ctx['filelines'] = content.splitlines()
        return render(request, 'codeeditor/main.html', ctx)


class AddFileView(View):
    def get(self, request, *args, **kwargs):
        return render(request, 'codeeditor/addfile.html', {'form': forms.AddFileForm()})

    def post(self, request, *args, **kwargs):
        if request.user.is_authenticated:
            form = forms.AddFileForm(request.POST)

            if form.is_valid():
                file = models.File(name=form.cleaned_data['name'],
                            description=form.cleaned_data['description'],
                            directory=form.cleaned_data['directory'],
                            owner=request.user)
                file.save()
                return HttpResponseRedirect('/file/' + str(file.pk))
            else:
                return render(request, 'codeeditor/addfile.html', {'form': form})
        else:
            return render(request, 'registration/login.html')


class AddSectionView(View):
    def get(self, request, *args, **kwargs):
        return render(request, 'codeeditor/addsection.html', {'form': forms.AddSectionForm()})

    def post(self, request, *args, **kwargs):
        if request.user.is_authenticated:
            form = forms.AddSectionForm(request.POST)

            if form.is_valid():
                statusData = models.SectionStatusData(content=form.cleaned_data['section_status_content'],
                                                      user=request.user)
                section = models.FileSection(name=form.cleaned_data['name'],
                                             description=form.cleaned_data['description'],
                                             section_category=form.cleaned_data['section_category'],
                                             section_status=form.cleaned_data['section_status'],
                                             section_status_data=statusData,
                                             content=form.cleaned_data['content'],
                                             is_subsection=form.cleaned_data['is_subsection'],
                                             parent_section=form.cleaned_data['parent_section'],
                                             parent_file=form.cleaned_data['parent_file'])
                statusData.save()
                try:
                    section.save()
                except Exception as e:
                    statusData.delete()
                    raise e

                file = section.get_file()

                return HttpResponseRedirect('/file/' + str(file.pk))
            else:
                return render(request, 'codeeditor/addsection.html', {'form': form})
        else:
            return render(request, 'registration/login.html')
