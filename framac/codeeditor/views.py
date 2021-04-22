from django.views import View
from django.shortcuts import render

from .models import Directory
from .models import File


class CodeEditorView(View):
    def get(self, request):
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

        return render(request, 'codeeditor/index.html', ctx)
