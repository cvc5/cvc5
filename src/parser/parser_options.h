#include "cvc4_public.h"

#ifndef __CVC4__PARSER__PARSER_OPTIONS_H
#define __CVC4__PARSER__PARSER_OPTIONS_H

namespace CVC4 {
namespace parser {

/** The input language option */
enum InputLanguage {
  /** The SMTLIB input language */
  LANG_SMTLIB,
  /** The CVC4 input language */
  LANG_CVC4,
  /** Auto-detect the language */
  LANG_AUTO
};/* enum InputLanguage */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_OPTIONS_H */
