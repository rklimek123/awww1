from django.contrib import admin
from .models import *

admin.site.register(Directory)
admin.site.register(File)
admin.site.register(FileSection)
admin.site.register(SectionCategory)
admin.site.register(SectionStatus)
admin.site.register(SectionStatusData)
admin.site.register(Prover)
