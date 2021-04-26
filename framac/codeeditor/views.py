import subprocess

from django.http import HttpResponseRedirect
from django.shortcuts import get_object_or_404, render
from django.urls import reverse
from django.views import View

import re

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


def get_separator():
    return "------------------------------------------------------------"


def parse_section(string):
    filesection = None
    proved_status = ""
    lines = string.splitlines()
    if string[2:6] == "Goal":
        lines_len = len(lines)
        line_number_line = lines[2]
        proved_status_line = lines[lines_len - 2]

        number_match = re.findall(r"line ([\d]+)\):$", line_number_line)

        if len(number_match) != 0:
            line_number = int(number_match[0])
            filesection = get_filesection(line_number)

        proved_match = re.findall(r"^Prover [\S]+ returns ([\S]+)", proved_status_line)
        if len(proved_match) != 0:
            proved_status = proved_match[0]

    result = []
    for line in lines:
        result.append(line)
    return result, filesection, proved_status  # (section string, FileSection matching this section, status)


def get_filesection(line_number):
    sections = models.FileSection.objects.filter(available=True, begin__lte=line_number, end__gte=line_number)
    if not sections.exists():
        return None
    else:
        best_section = None  # best section is the one which is the shortest (the most specific)
        for section in sections:
            if best_section is None or best_section.end - best_section.begin > section.end - section.begin:
                best_section = section
        return best_section.get_hierarchy_name()


def parse_frama_output(raw):
    separator = get_separator()
    sep_len = len(separator)
    sections = []

    last_index = raw.find(separator)
    while last_index != -1:
        string = raw[:last_index]
        sections.append(parse_section(string))

        raw = raw[last_index + sep_len:]
        last_index = raw.find(separator)

    sections.append(parse_section(raw))
    return sections


class CodeEditorViewSelected(CodeEditorViewBlank):
    def get(self, request, *args, **kwargs):
        file_id = kwargs['id']
        ctx = self.get_context()
        file = get_object_or_404(models.File, pk=file_id, available=True)

        # Filesystem view
        ctx['selected_file'] = file

        # Code edit (main) view
        ctx['filelines'] = file.get_content()

        # Focus on program elements view
        framac_call = 'frama-c -wp -wp-print ' + 'upload/' + file.content.name
        result = subprocess.getstatusoutput(framac_call)
        if result[0] != 0:
            ctx['error_msg'] = "Frama encountered an error"
        else:
            result = result[1]
            ctx['sections'] = parse_frama_output(result)
            ctx['separator'] = get_separator()

        return render(request, 'codeeditor/main.html', ctx)


class AddFileView(View):
    def get(self, request, *args, **kwargs):
        return render(request,
                      'codeeditor/form.html',
                      {'form': forms.AddFileForm(),
                       'action': reverse('addfile')})

    def post(self, request, *args, **kwargs):
        if request.user.is_authenticated:
            form = forms.AddFileForm(request.POST, request.FILES)

            if form.is_valid():
                file = models.File(name=form.cleaned_data['content'].name,
                                   description=form.cleaned_data['description'],
                                   content=form.cleaned_data['content'],
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
                                             begin=form.cleaned_data['begin'],
                                             end=form.cleaned_data['end'],
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
