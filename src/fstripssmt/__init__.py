
import logging
from .version import __version__, __version_info__

logging.getLogger(__name__).addHandler(logging.NullHandler())
