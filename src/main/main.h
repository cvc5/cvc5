#include <iostream>
#include <exception>
#include <string>

#include "config.h"
#include "util/exception.h"
#include "util/options.h"

#ifndef __CVC4_MAIN_H
#define __CVC4_MAIN_H

namespace CVC4 {
namespace Main {

class OptionException : public CVC4::Exception {
public:
  OptionException(const std::string& s) throw() : CVC4::Exception("Error in option parsing: " + s) {}
};/* class OptionException */

int parseOptions(int argc, char** argv, CVC4::Options*) throw(CVC4::Exception*);
void cvc4_init() throw();

}/* CVC4::Main namespace */
}/* CVC4 namespace */

#endif /* __CVC4_MAIN_H */
