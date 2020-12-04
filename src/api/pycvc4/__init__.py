import sys
from .pycvc4 import *
# fake a submodule for dotted imports, e.g. from pycvc4.kinds import *
sys.modules['%s.%s'%(__name__, kinds.__name__)] = kinds
