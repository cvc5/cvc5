#include "options/outputc.h"

#include <iostream>

namespace cvc5 {

OutputC OutputChannel(&std::cout);

Cvc5ostream OutputC::operator()(const options::OutputTag tag) const
{
  if (options::outputTagHolder()[static_cast<size_t>(tag)])
  {
    return Cvc5ostream(d_os);
  }
  else
  {
    return Cvc5ostream();
  }
}

Cvc5ostream OutputC::operator()(const std::string& tag) const
{
  return (*this)(options::stringToOutputTag(tag));
}

bool OutputC::isOn(const options::OutputTag tag) const
{
  return options::outputTagHolder()[static_cast<size_t>(tag)];
}
bool OutputC::isOn(const std::string& tag) const
{
  return (*this).isOn(options::stringToOutputTag(tag));
}

}  // namespace cvc5
