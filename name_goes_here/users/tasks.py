from django.contrib.auth import get_user_model
from django.core import management

from config import celery_app

User = get_user_model()


@celery_app.task()
def get_users_count():
    """A pointless Celery task to demonstrate usage."""
    return User.objects.count()


@celery_app.task()
def clear_expired_refresh_tokens():
    """Removes expired refresh tokens from db."""
    return management.call_command("cleartokens", expired=True)
