from django.conf import settings
from django.conf.urls.static import static
from django.contrib import admin
from django.urls import include, path
from django.views.decorators.csrf import csrf_exempt
from drf_spectacular.views import SpectacularAPIView, SpectacularSwaggerView

from name_goes_here.graphql.schema import schema
from name_goes_here.graphql.views import GraphQLView

urlpatterns = [
    # Django Admin, use {% url 'admin:index' %}
    path(settings.ADMIN_URL, admin.site.urls),
    # Graphql url
    path("graphql/", csrf_exempt(GraphQLView.as_view(graphiql=settings.GRAPHIQL, schema=schema))),
    # REST API base url
    path("api/", include("name_goes_here.rest.api_router")),
    # REST API schema
    path("api/schema/", SpectacularAPIView.as_view(), name="api-schema"),
    # REST API docs
    path(
        "api/docs/",
        SpectacularSwaggerView.as_view(url_name="api-schema"),
        name="api-docs",
    ),
] + static(settings.MEDIA_URL, document_root=settings.MEDIA_ROOT)


if settings.PLUGGABLE_FUNCS.DEBUG_TOOLBAR:
    import debug_toolbar

    urlpatterns.append(
        path("__debug__/", include(debug_toolbar.urls)),
    )
