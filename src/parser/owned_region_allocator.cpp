#include "parser/owned_region_allocator.h"

#include <cassert>
#include <cstdlib>
#include <cstring>

namespace CVC4 {
namespace parser {

OwnedRegionAllocator::OwnedRegionAllocator() : d_regions() {}

OwnedRegionAllocator::~OwnedRegionAllocator() {
  for (size_t i = 0; i < d_regions.size(); ++i) {
    free(d_regions[i]);
  }
}

void* OwnedRegionAllocator::mallocRegion(const size_t size) {
  void* region = malloc(size);
  assert(region != NULL);
  takeOwnership(region);
  return region;
}

// Reallocates a `region` of memory containing `size` bytes into a larger
// region of size `next_size` bytes and takes ownership of the region.
void* OwnedRegionAllocator::reallocRegion(void* region, const size_t size,
                                          const size_t next_size) {
  assert(size <= next_size);
  void* new_copy = mallocRegion(next_size);
  memcpy(new_copy, region, size);
  return new_copy;
}

void OwnedRegionAllocator::takeOwnership(void* region) {
  d_regions.push_back(region);
}

}  // namespace parser
}  // namespace CVC4
