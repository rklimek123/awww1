from django.views import View
from django.shortcuts import render

from .models import Directory
from .models import File


class CodeEditorViewBlank(View):
    def get_context(self):
        ctx = {}
        ctx['inroot_dirs'] = Directory.objects.filter(parent=None).order_by('name')
        ctx['inroot_files'] = File.objects.filter(directory=None).order_by('name')
        ctx['in_dirs'] = {}
        ctx['in_files'] = {}
        for direct in Directory.objects.all():
            children_dirs = Directory.objects.filter(parent=direct).order_by('name')
            children_files = File.objects.filter(directory=direct).order_by('name')
            ctx['in_dirs'][direct] = children_dirs
            ctx['in_files'][direct] = children_files
        return ctx

    def get(self, request):
        return render(request, 'codeeditor/index.html', self.get_context())


class CodeEditorViewSelected(CodeEditorViewBlank):
    def get(self, request, *args, **kwargs):
        file_id = kwargs['id']
        ctx = self.get_context()
        ctx['selected_file'] = File.objects.get(pk=file_id)
        content = ctx['selected_file'].content
        ctx['filelines'] = content.splitlines()
        return render(request, 'codeeditor/main.html', ctx)
