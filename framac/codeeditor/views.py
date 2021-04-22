from django.views import View
from django.shortcuts import render


class CodeEditorView(View):
    def get(self, request):
        return render(request, 'codeeditor/index.html')
