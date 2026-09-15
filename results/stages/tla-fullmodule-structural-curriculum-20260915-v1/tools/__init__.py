import os

__path__.extend(
    path for path in os.environ.get('TLA_TOOLS_PATHS', '').split(':') if path
)
