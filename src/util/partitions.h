#include <vector>
#include <algorithm>

namespace CVC4 {
namespace util {

class partition
{
public:
  class iterator
  {
  public:
    /** 
     * iterate over all partitions of [0, 1, ... n-1] (same as
     * generating equivalence relations)
     * 
     * corresponds to n-th bell number (A000110 in OEIS)
     */
    iterator(unsigned n, bool first = true);

    unsigned  size()     const { return kappa.size();      }

    /** How many partitions does the current paritioning use */
    unsigned  subsets()  const { return M[size() - 1] + 1; }

    /** Which partition is 'i' in? Numbering starts with 0. */
    int get(int i) { return kappa[i]; }

    /** Are 'i' and 'j' in the same partition */
    bool equal(int i, int j) { return kappa[i] == kappa[j]; }

    /** go to next partitioning */
    iterator& operator++();

    bool isFinished() { return d_finished; }
  protected:
    std::vector<unsigned> kappa, M;
    bool d_finished;
  };
};

/**
   Implementation from
   https://www.cs.bgu.ac.il/~orlovm/papers/partitions-source.tar.gz

   Released in public domain by Michael Orlov <orlovm@cs.bgu.ac.il>,
   according to the accompaning paper (Efficient Generation of Set
   Partitions, Appendix A).

   --Kshitij Bansal, Tue Aug  5 15:57:20 EDT 2014
*/

partition::iterator::
iterator(unsigned n, bool first)
  : kappa(n), M(n), d_finished(false)
{
  if (n <= 0)
    throw std::invalid_argument
      ("partition::iterator: n must be positive");

  if (! first)
    for (unsigned i = 1; i < n; ++i) {
      kappa[i] = i;
      M[i] = i;
    }
}

partition::iterator&
partition::iterator::
operator++()
{
  const unsigned n = size();

  for (unsigned i = n-1; i > 0; --i)
    if (kappa[i] <= M[i-1]) {
      ++kappa[i];

      const unsigned new_max = std::max(M[i], kappa[i]);
      M[i] = new_max;
      for (unsigned j = i + 1; j < n; ++j) {
        kappa[j] = 0;
        M[j] = new_max;
      }

      // integrityCheck();
      return *this;
    }

  d_finished = true;
  return *this;
}

}
}
