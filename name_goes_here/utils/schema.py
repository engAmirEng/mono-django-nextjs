import graphene


class IError(graphene.Interface):
    """
    The Interface for handling errors
    """

    message = graphene.String(required=True)
