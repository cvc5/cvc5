###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

cvc5_add_api_test(issue11069 "issues")
cvc5_add_api_test(issue5074 "issues")
cvc5_add_api_test(issue5893 "issues")
cvc5_add_api_test(issue6111 "issues")
cvc5_add_api_test(issue7000 "issues")
cvc5_add_api_test(proj-issue306 "issues")
cvc5_add_api_test(proj-issue308 "issues")
cvc5_add_api_test(proj-issue334 "issues")
cvc5_add_api_test(proj-issue337 "issues")
cvc5_add_api_test(proj-issue373 "issues")
cvc5_add_api_test(proj-issue378 "issues")
cvc5_add_api_test(proj-issue379 "issues")
cvc5_add_api_test(proj-issue381 "issues")
cvc5_add_api_test(proj-issue382 "issues")
cvc5_add_api_test(proj-issue383 "issues")
cvc5_add_api_test(proj-issue386 "issues")
cvc5_add_api_test(proj-issue388 "issues")
cvc5_add_api_test(proj-issue395 "issues")
cvc5_add_api_test(proj-issue399 "issues")
cvc5_add_api_test(proj-issue414 "issues")
cvc5_add_api_test(proj-issue420 "issues")
cvc5_add_api_test(proj-issue423 "issues")
cvc5_add_api_test(proj-issue429 "issues")
cvc5_add_api_test(proj-issue431 "issues")
cvc5_add_api_test(proj-issue434 "issues")
cvc5_add_api_test(proj-issue435 "issues")
cvc5_add_api_test(proj-issue455 "issues")
cvc5_add_api_test(proj-issue484 "issues")
cvc5_add_api_test(proj-issue538 "issues")
cvc5_add_api_test(proj-issue570 "issues")
cvc5_add_api_test(proj-issue575 "issues")
cvc5_add_api_test(proj-issue654 "issues")
cvc5_add_api_test(proj-issue655 "issues")
cvc5_add_api_test(proj-issue666 "issues")

if (NOT ENABLE_SAFE_MODE)
  cvc5_add_api_test(issue4889 "issues")
  cvc5_add_api_test(proj-issue344 "issues")
  cvc5_add_api_test(proj-issue345 "issues")
  cvc5_add_api_test(proj-issue377 "issues")
  cvc5_add_api_test(proj-issue413 "issues")
  cvc5_add_api_test(proj-issue416 "issues")
  cvc5_add_api_test(proj-issue418 "issues")
  cvc5_add_api_test(proj-issue421 "issues")
  cvc5_add_api_test(proj-issue422 "issues")
  cvc5_add_api_test(proj-issue426 "issues")
  cvc5_add_api_test(proj-issue436 "issues")
  cvc5_add_api_test(proj-issue440 "issues")
  cvc5_add_api_test(proj-issue445 "issues")
  cvc5_add_api_test(proj-issue567 "issues")
  cvc5_add_api_test(proj-issue573 "issues")
  cvc5_add_api_test(proj-issue574 "issues")
  cvc5_add_api_test(proj-issue576 "issues")
  cvc5_add_api_test(proj-issue580 "issues")
  cvc5_add_api_test(proj-issue581 "issues")
  cvc5_add_api_test(proj-issue587 "issues")
  cvc5_add_api_test(proj-issue600 "issues")
  cvc5_add_api_test(proj-issue611 "issues")
  cvc5_add_api_test(proj-issue612 "issues")
  cvc5_add_api_test(proj-issue618 "issues")
  cvc5_add_api_test(proj-issue621 "issues")
  cvc5_add_api_test(proj-issue644 "issues")
  cvc5_add_api_test(proj-issue646 "issues")
  cvc5_add_api_test(proj-issue652 "issues")
  cvc5_add_api_test(proj-issue656 "issues")
  cvc5_add_api_test(proj-issue657 "issues")
endif()
