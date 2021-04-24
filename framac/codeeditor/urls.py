from django.urls import include, path

from . import views
from django.contrib.auth import views as login_views

urlpatterns = [
    path('', views.CodeEditorViewBlank.as_view(), name='index'),
    path('file/<int:id>', views.CodeEditorViewSelected.as_view(), name='main'),
    path('addfile/', views.AddFileView.as_view(), name='addfile'),
    path('addsection/', views.AddSectionView.as_view(), name='addsection'),
    path('login/', login_views.LoginView.as_view(), name='login'),
    path('logout/', login_views.LogoutView.as_view(), name='logout'),
]