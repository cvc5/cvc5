/*
 * parser_options.h
 *
 *  Created on: Mar 3, 2010
 *      Author: chris
 */

#ifndef CVC4__PARSER__PARSER_OPTIONS_H_
#define CVC4__PARSER__PARSER_OPTIONS_H_

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
  };

}
}

#endif /* CVC4__PARSER__PARSER_OPTIONS_H_ */
