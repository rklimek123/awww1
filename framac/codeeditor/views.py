import subprocess

from django.http import HttpResponseRedirect
from django.shortcuts import get_object_or_404, render
from django.urls import reverse
from django.views import View

import re

from . import models
from . import forms


class CodeEditorViewBlank(View):
    def get_context(self, request, *args, **kwargs):
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

    def get(self, request, *args, **kwargs):
        ctx = self.get_context(request, *args, **kwargs)
        return render(request, 'codeeditor/index.html', ctx)


def get_separator():
    return "------------------------------------------------------------"


def parse_section(string, file):
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
            filesection = get_filesection(line_number, file)

        proved_match = re.findall(r"^Prover [\S]+ returns ([\S]+)", proved_status_line)
        if len(proved_match) != 0:
            proved_status = proved_match[0]

    result = []
    for line in lines:
        result.append(line)
    return result, filesection, proved_status  # (section string, FileSection matching this section, status)


def get_filesection(line_number, file):
    sections = models.FileSection.objects.filter(available=True,
                                                 parent_file=file,
                                                 begin__lte=line_number,
                                                 end__gte=line_number)
    if not sections.exists():
        return None
    else:
        best_section = None  # best section is the one which is the shortest (the most specific)
        for section in sections:
            if best_section is None or best_section.end - best_section.begin > section.end - section.begin:
                best_section = section
        return best_section.get_hierarchy_name()


def parse_frama_output(raw, file):
    separator = get_separator()
    sep_len = len(separator)
    sections = []

    last_index = raw.find(separator)
    while last_index != -1:
        string = raw[:last_index]
        sections.append(parse_section(string, file))

        raw = raw[last_index + sep_len:]
        last_index = raw.find(separator)

    sections.append(parse_section(raw, file))
    return sections

def get_result_tab(file):
    framac_call = 'frama-c -wp -wp-log="r:result.txt" upload/' + file.content.name

    result = subprocess.getstatusoutput(framac_call)
    if result[0] != 0:
        return "Frama encountered an error\n" + result[1], 1
    else:
        result_file = open('result.txt', "r")
        result = result_file.readlines()
        result_file.close()
        return result, 0


class CodeEditorPreVerification(CodeEditorViewBlank):
    def get_context(self, request, *args, **kwargs):
        ctx = super().get_context(request, *args, **kwargs)
        file_id = kwargs['id']
        file = get_object_or_404(models.File, pk=file_id, available=True)

        # Filesystem view
        ctx['selected_file'] = file

        # Code edit (main) view
        ctx['filelines'] = file.get_content()
        ctx['tab'] = int(request.GET.get('tab', "2"))
        ctx['result_tab'] = get_result_tab(file)
        return ctx

    def get(self, request, *args, **kwargs):
        ctx = self.get_context(request, *args, **kwargs)
        ctx['provers_form'] = forms.ChooseProverForm()
        ctx['vcs_form'] = forms.ChooseVcForm()
        return render(request, 'codeeditor/main.html', ctx)

    def post(self, request, *args, **kwargs):
        if request.user.is_authenticated:
            prover = request.POST.get('prover', None)
            vc = request.POST.get('vc', None)
            rte = request.POST.get('rte', None)
            file = get_object_or_404(models.File, pk=kwargs['id'], available=True)

            if prover is not None:
                if prover == '':
                    file.prover = None
                else:
                    file.prover = models.Prover.objects.get(pk=int(prover))
            elif vc is not None:
                file.vcs = vc

                if rte is not None:
                    file.rte = True
                else:
                    file.rte = False
            else:
                raise Exception("503 - Bad Request (POST)")
            file.save()
            return HttpResponseRedirect(reverse('noframa', kwargs={'id': file.pk}))
        else:
            return HttpResponseRedirect(reverse('login'))


class CodeEditorViewSelected(CodeEditorPreVerification):
    def get_context(self, request, *args, **kwargs):
        ctx = super().get_context(request, *args, **kwargs)
        ctx['separator'] = get_separator()

        file = ctx['selected_file']

        # Focus on program elements view
        if int(request.GET.get('custom', 0)) == 1:
            framac_call = 'frama-c -wp -wp-print -wp-prover '
            if file.prover is None:
                framac_call += " alt-ergo"
            else:
                framac_call += " " + file.prover.arg

            if file.vcs is not None and file.vcs != '':
                framac_call += ' -wp-prop="' + file.vcs + '"'

            if file.rte is not None and file.rte:
                framac_call += " -wp-rte"

            framac_call += " upload/" + file.content.name
        else:
            framac_call = 'frama-c -wp -wp-print upload/' + file.content.name

        result = subprocess.getstatusoutput(framac_call)
        if result[0] != 0:
            ctx['error_msg'] = "Frama encountered an error\n" + result[1]
        else:
            result = result[1]
            ctx['sections'] = parse_frama_output(result, file)
        return ctx

    def get(self, request, *args, **kwargs):
        ctx = self.get_context(request, *args, **kwargs)
        print(request.GET)
        ctx['tab'] = 2
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
            return HttpResponseRedirect(reverse('login'))


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
                file = form.cleaned_data['parent_file']
                if file is None:
                    file = form.cleaned_data['parent_section'].parent_file
                section = models.FileSection(name=form.cleaned_data['name'],
                                             description=form.cleaned_data['description'],
                                             section_category=form.cleaned_data['section_category'],
                                             section_status=form.cleaned_data['section_status'],
                                             section_status_data=status_data,
                                             begin=form.cleaned_data['begin'],
                                             end=form.cleaned_data['end'],
                                             is_subsection=form.cleaned_data['is_subsection'],
                                             parent_section=form.cleaned_data['parent_section'],
                                             parent_file=file)
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
            return HttpResponseRedirect(reverse('login'))


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
            return HttpResponseRedirect(reverse('login'))


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
            return HttpResponseRedirect(reverse('login'))


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
            return HttpResponseRedirect(reverse('login'))
