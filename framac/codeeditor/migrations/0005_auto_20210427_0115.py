# Generated by Django 3.1.7 on 2021-04-27 01:15

from django.db import migrations, models
import django.db.models.deletion


class Migration(migrations.Migration):

    dependencies = [
        ('codeeditor', '0004_auto_20210426_2340'),
    ]

    operations = [
        migrations.CreateModel(
            name='Vc',
            fields=[
                ('id', models.AutoField(auto_created=True, primary_key=True, serialize=False, verbose_name='ID')),
                ('name', models.TextField(max_length=50)),
                ('creation_date', models.DateTimeField(auto_now_add=True)),
                ('modify_date', models.DateTimeField(auto_now=True)),
                ('available', models.BooleanField(default=True)),
            ],
        ),
        migrations.AddField(
            model_name='file',
            name='rte',
            field=models.BooleanField(default=False),
        ),
        migrations.AlterField(
            model_name='filesection',
            name='parent_file',
            field=models.ForeignKey(default=None, limit_choices_to={'available': True}, on_delete=django.db.models.deletion.CASCADE, to='codeeditor.file'),
            preserve_default=False,
        ),
        migrations.AddField(
            model_name='file',
            name='vcs',
            field=models.ForeignKey(blank=True, limit_choices_to={'available': True}, null=True, on_delete=django.db.models.deletion.SET_NULL, to='codeeditor.vc'),
        ),
    ]
