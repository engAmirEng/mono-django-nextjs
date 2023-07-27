from pathlib import Path

import environ
from django.core.exceptions import ImproperlyConfigured

BASE_DIR = Path(__file__).resolve(strict=True).parent.parent.parent
# name_goes_here/
APPS_DIR = BASE_DIR / "name_goes_here"


# handy funcs
def clean_ellipsis(items: iter):
    return [i for i in items if i is not ...]


env = environ.Env()

READ_DOT_ENV_FILE = env.bool("DJANGO_READ_DOT_ENV_FILE", default=False)
if READ_DOT_ENV_FILE:
    from merge_dotenvs_in_dotenv import DOTENV_FILE, DOTENV_FILES, merge

    merge(DOTENV_FILE, DOTENV_FILES)
    # OS environment variables take precedence over variables from .env
    env.read_env(DOTENV_FILE)


# Define pluggable functionalities
pluggable_available = ["DEBUG_TOOLBAR", "NO_PASS_VALIDATION", "SERVE_STATICFILES", "EXTENSIONS"]
pluggable_enabled = env.list("PLUGGABLES")
for p in pluggable_enabled:
    if p not in pluggable_available:
        raise ImproperlyConfigured(f"{p} is not a pluggable option")


class PLUGGABLE_FUNCS:
    DEBUG_TOOLBAR = "DEBUG_TOOLBAR" in pluggable_enabled
    NO_PASS_VALIDATION = "NO_PASS_VALIDATION" in pluggable_enabled
    SERVE_STATICFILES = "SERVE_STATICFILES" in pluggable_enabled
    EXTENSIONS = "EXTENSIONS" in pluggable_enabled
