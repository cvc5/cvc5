#include "options/outputc.h"

#include <iostream>

namespace cvc5 {

OutputC OutputChannel(&std::cout);

Cvc5ostream OutputC::operator()(const Options& opts,
                                const options::OutputTag tag) const
{
  if (opts.base.outputTagHolder[static_cast<size_t>(tag)])
  {
    return Cvc5ostream(d_os);
  }
  else
  {
    return Cvc5ostream();
  }
}

Cvc5ostream OutputC::operator()(const options::OutputTag tag) const
{
  return (*this)(Options::current(), tag);
}

bool OutputC::isOn(const Options& opts, const options::OutputTag tag) const
{
  return opts.base.outputTagHolder[static_cast<size_t>(tag)];
}
bool OutputC::isOn(const options::OutputTag tag) const
{
  return isOn(Options::current(), tag);
}

}  // namespace cvc5
