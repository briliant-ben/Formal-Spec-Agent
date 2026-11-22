"""Optional model providers; deterministic validation has no provider dependency."""
from .deepseek import request as deepseek_request
from .gemini import request as gemini_request

DEFAULT_PROVIDER = 'gemini'
PROVIDERS = {
    'gemini': gemini_request,
    'deepseek': deepseek_request,
}


def get_provider(name):
    """Return the provider request function for a supported provider name."""
    if name not in PROVIDERS:
        supported = ', '.join(sorted(PROVIDERS))
        raise ValueError(f'Unsupported model provider {name!r}; expected one of: {supported}')
    return PROVIDERS[name]

