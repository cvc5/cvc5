#include "equality_engine.h"

using namespace CVC4::theory::bv;

const size_t NodeIdTraits::null = ((size_t)(-1) << (sizeof(size_t)*8 - NodeIdTraits::s_id_bits)) >> (sizeof(size_t)*8 - NodeIdTraits::s_id_bits);
