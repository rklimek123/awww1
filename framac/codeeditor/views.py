from django.contrib.auth.models import User
from django.http import HttpResponseRedirect
from django.views import View
from django.shortcuts import get_object_or_404, render

from .models import Directory
from .models import File
from .forms import AddFileForm

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
        ctx['selected_file'] = get_object_or_404(File, pk=file_id)
        #content = ctx['selected_file'].content
        #ctx['filelines'] = content.splitlines()
        return render(request, 'codeeditor/main.html', ctx)


class AddFileView(View):
    def get(self, request, *args, **kwargs):
        return render(request, 'codeeditor/addfile.html', {'form': AddFileForm()})

    def post(self, request, *args, **kwargs):
        if request.user.is_authenticated:
            form = AddFileForm(request.POST)

            if form.is_valid():
                file = File(name=form.cleaned_data['file_name'],
                            description=form.cleaned_data['description'],
                            directory=form.cleaned_data['directory'],
                            owner=User.objects.get(pk=request.user.pk))
                file.save()
                return HttpResponseRedirect('/file/' + str(file.pk))
            else:
                return render(request, 'codeeditor/addfile.html', {'form': form})
        else:
            return render(request, 'registration/login.html')

