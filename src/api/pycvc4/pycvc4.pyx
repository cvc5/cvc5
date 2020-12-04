include "cvc4kinds.pxi"
include "cvc4.pxi"

import sys
# fake a submodule for dotted imports, e.g. from pycvc4.kinds import *
sys.modules['pycvc4.kinds'] = kinds
