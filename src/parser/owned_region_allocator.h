#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__OWNED_REGION_ALLOCATOR_H
#define __CVC4__PARSER__OWNED_REGION_ALLOCATOR_H

#include <cstddef>

#include <vector>

namespace CVC4 {
namespace parser {

// A class that allocates memory regions, maintains ownership of these regions,
// frees all regions at its destruction time.
class OwnedRegionAllocator {
 public:
  OwnedRegionAllocator();
  ~OwnedRegionAllocator();

  // Allocates a region of size `size` and maintains ownership of it.
  void* mallocRegion(size_t size);

  // Reallocates a `region` of memory containing `size` bytes into a larger
  // region of size `next_size` bytes and owns the new region.
  //
  // assert()-fails if size is larger than next_size.
  void* reallocRegion(void* region, size_t size, size_t next_size);

 private:
  // Takes ownership of the given memory region.
  void takeOwnership(void* region);

  // Regions of memory;
  std::vector<void*> d_regions;
};

}  // namespace parser
}  // namespace CVC4

#endif /* #define __CVC4__PARSER__OWNED_REGION_ALLOCATOR_H */
