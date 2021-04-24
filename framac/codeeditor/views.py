from django.http import HttpResponseRedirect
from django.shortcuts import get_object_or_404, render
from django.urls import reverse
from django.views import View

from . import models
from . import forms


class CodeEditorViewBlank(View):
    def get_context(self):
        ctx = {}
        ctx['inroot_dirs'] = models.Directory.objects.filter(parent=None, available=True).order_by('name')
        ctx['inroot_files'] = models.File.objects.filter(directory=None, available=True).order_by('name')
        ctx['in_dirs'] = {}
        ctx['in_files'] = {}
        for direct in models.Directory.objects.all():
            children_dirs = models.Directory.objects.filter(parent=direct, available=True).order_by('name')
            children_files = models.File.objects.filter(directory=direct, available=True).order_by('name')
            ctx['in_dirs'][direct] = children_dirs
            ctx['in_files'][direct] = children_files
        return ctx

    def get(self, request):
        return render(request, 'codeeditor/index.html', self.get_context())


class CodeEditorViewSelected(CodeEditorViewBlank):
    def get(self, request, *args, **kwargs):
        file_id = kwargs['id']
        ctx = self.get_context()
        file = get_object_or_404(models.File, pk=file_id, available=True)
        ctx['selected_file'] = file
        content = file.get_content()
        ctx['filelines'] = content.splitlines()
        return render(request, 'codeeditor/main.html', ctx)


class AddFileView(View):
    def get(self, request, *args, **kwargs):
        return render(request,
                      'codeeditor/form.html',
                      {'form': forms.AddFileForm(),
                       'action': reverse('addfile')})

    def post(self, request, *args, **kwargs):
        if request.user.is_authenticated:
            form = forms.AddFileForm(request.POST)

            if form.is_valid():
                file = models.File(name=form.cleaned_data['name'],
                                   description=form.cleaned_data['description'],
                                   directory=form.cleaned_data['directory'],
                                   owner=request.user)
                file.save()
                return HttpResponseRedirect(reverse('main', kwargs={'id': file.pk}))
            else:
                return render(request, 'codeeditor/form.html', {'form': form, 'action': reverse('addfile')})
        else:
            return render(request, 'registration/login.html')


class AddSectionView(View):
    def get(self, request, *args, **kwargs):
        return render(request,
                      'codeeditor/form.html',
                      {'form': forms.AddSectionForm(),
                       'action': reverse('addsection')})

    def post(self, request, *args, **kwargs):
        if request.user.is_authenticated:
            form = forms.AddSectionForm(request.POST)

            if form.is_valid():
                status_data = models.SectionStatusData(content=form.cleaned_data['section_status_content'],
                                                       user=request.user)
                section = models.FileSection(name=form.cleaned_data['name'],
                                             description=form.cleaned_data['description'],
                                             section_category=form.cleaned_data['section_category'],
                                             section_status=form.cleaned_data['section_status'],
                                             section_status_data=status_data,
                                             content=form.cleaned_data['content'],
                                             is_subsection=form.cleaned_data['is_subsection'],
                                             parent_section=form.cleaned_data['parent_section'],
                                             parent_file=form.cleaned_data['parent_file'])
                status_data.save()
                try:
                    section.save()
                except Exception as e:
                    status_data.delete()
                    raise e

                file = section.get_file()

                return HttpResponseRedirect(reverse('main', kwargs={'id': file.pk}))
            else:
                return render(request,
                              'codeeditor/form.html',
                              {'form': form,
                               'action': reverse('addsection')})
        else:
            return render(request, 'registration/login.html')


class AddDirectoryView(View):
    def get(self, request, *args, **kwargs):
        return render(request,
                      'codeeditor/form.html',
                      {'form': forms.AddDirectoryForm(),
                       'action': reverse('adddirectory')})

    def post(self, request, *args, **kwargs):
        if request.user.is_authenticated:
            form = forms.AddDirectoryForm(request.POST)

            if form.is_valid():
                directory = models.Directory(name=form.cleaned_data['name'],
                                             description=form.cleaned_data['description'],
                                             owner=request.user,
                                             parent=form.cleaned_data['parent'])
                directory.save()
                return HttpResponseRedirect(reverse('index'))
            else:
                return render(request,
                              'codeeditor/form.html',
                              {'form': form,
                               'action': reverse('adddirectory')})
        else:
            return render(request, 'registration/login.html')


class DeleteFileView(View):
    def get(self, request, *args, **kwargs):
        return render(request,
                      'codeeditor/form.html',
                      {'form': forms.DeleteFileForm(),
                       'action': reverse('deletefile')})

    def post(self, request, *args, **kwargs):
        if request.user.is_authenticated:
            form = forms.DeleteFileForm(request.POST)

            if form.is_valid():
                file = form.cleaned_data['file']
                file.mark_inavailable()
                return HttpResponseRedirect(reverse('index'))
            else:
                return render(request,
                              'codeeditor/form.html',
                              {'form': form,
                               'action': reverse('deletefile')})
        else:
            return render(request, 'registration/login.html')


class DeleteDirectoryView(View):
    def get(self, request, *args, **kwargs):
        return render(request,
                      'codeeditor/form.html',
                      {'form': forms.DeleteDirectoryForm(),
                       'action': reverse('deletedirectory')})

    def post(self, request, *args, **kwargs):
        if request.user.is_authenticated:
            form = forms.DeleteDirectoryForm(request.POST)

            if form.is_valid():
                directory = form.cleaned_data['directory']
                directory.mark_inavailable()
                return HttpResponseRedirect(reverse('index'))
            else:
                return render(request,
                              'codeeditor/form.html',
                              {'form': form,
                               'action': reverse('deletedirectory')})
        else:
            return render(request, 'registration/login.html')
