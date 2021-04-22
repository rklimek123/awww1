from django.urls import include, path

from .views import CodeEditorViewBlank
from .views import CodeEditorViewSelected

urlpatterns = [
    path('', CodeEditorViewBlank.as_view(), name='index'),
    path('file/<int:id>', CodeEditorViewSelected.as_view(), name='main'),
]