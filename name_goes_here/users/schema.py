import graphene
import graphql_jwt
from graphene_django import DjangoObjectType

from name_goes_here.utils.schema import IError

from .models import User


class JWTMutation:
    token_auth = graphql_jwt.ObtainJSONWebToken.Field()
    verify_token = graphql_jwt.Verify.Field()
    refresh_token = graphql_jwt.Refresh.Field()
    revoke_token = graphql_jwt.Revoke.Field()


# Error types
# ------------------------------------------------------------------------------
class PermissionDeniedErrorType(graphene.ObjectType):
    required_perm = graphene.String(required=True)

    class Meta:
        interfaces = (IError,)


class NotAuthorizedErrorType(graphene.ObjectType):
    class Meta:
        interfaces = (IError,)


# Model types
# ------------------------------------------------------------------------------
class UserType(DjangoObjectType):
    class Meta:
        model = User
        fields = "__all__"


class UserResult(graphene.Union):
    class Meta:
        types = (UserType, NotAuthorizedErrorType)


class Query:
    users = graphene.List(UserResult)

    def resolve_users(root, info, **kwargs):
        return User.objects.all()


class Mutation(JWTMutation):
    pass
