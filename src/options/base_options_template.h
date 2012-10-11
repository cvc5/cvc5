/*********************                                                        */
/*! \file base_options_template.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Contains code for handling command-line options.
 **
 ** Contains code for handling command-line options
 **/

#include "cvc4_public.h"

#ifndef __CVC4__OPTIONS__${module_id}_H
#define __CVC4__OPTIONS__${module_id}_H

#include "options/options.h"
${module_includes}

#line 28 "${template}"

${module_optionholder_spec}

#line 32 "${template}"

namespace CVC4 {

namespace options {

${module_decls}

#line 40 "${template}"

}/* CVC4::options namespace */

${module_specializations}

#line 46 "${template}"

namespace options {

${module_inlines}

#line 52 "${template}"

}/* CVC4::options namespace */

}/* CVC4 namespace */

#endif /* __CVC4__OPTIONS__${module_id}_H */
