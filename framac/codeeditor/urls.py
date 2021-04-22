from django.urls import include, path

from .views import CodeEditorView

urlpatterns = [
    path('', CodeEditorView.as_view(), name='index'),
]