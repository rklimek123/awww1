from django import template

register = template.Library()


@register.filter(name='range')
def range_pipe(number):
    return range(number)
