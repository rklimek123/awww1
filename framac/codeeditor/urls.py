from django.urls import include, path

from .views import CodeEditorViewBlank
from .views import CodeEditorViewSelected
from django.contrib.auth import views as login_views

urlpatterns = [
    path('', CodeEditorViewBlank.as_view(), name='index'),
    path('file/<int:id>', CodeEditorViewSelected.as_view(), name='main'),
    path('login/', login_views.LoginView.as_view(), name='login'),
    path('logout/', login_views.LogoutView.as_view(), name='logout'),
]