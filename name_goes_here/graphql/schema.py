import graphene
from django.conf import settings
from graphene_django.debug import DjangoDebug


class Query(graphene.ObjectType):
    if settings.PLUGGABLE_FUNCS.DEBUG_TOOLBAR:
        debug = graphene.Field(DjangoDebug, name="_debug")

    hello = graphene.String(default_value="Hi!")


schema = graphene.Schema(query=Query)
