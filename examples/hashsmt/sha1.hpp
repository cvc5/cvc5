/*********************                                                        */
/*! \file sha1.hpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

// boost/uuid/sha1.hpp header file  ----------------------------------------------//

// Copyright 2007 Andy Tompkins.
// Distributed under the Boost Software License, Version 1.0. (See
// accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

// Revision History
//  29 May 2007 - Initial Revision
//  25 Feb 2008 - moved to namespace boost::uuids::detail

// This is a byte oriented implementation
// Note: this implementation does not handle message longer than
//       2^32 bytes.

#ifndef __CVC4__EXAMPLES__HASHSMT__SHA1_H
#define __CVC4__EXAMPLES__HASHSMT__SHA1_H

#include <cstddef>

#include "word.h"

#ifdef BOOST_NO_STDC_NAMESPACE
namespace std {
    using ::size_t;
} // namespace std
#endif

namespace hashsmt {

static_assert(sizeof(unsigned char)*8 == 8,
              "Unexpected size for unsigned char");
static_assert(sizeof(unsigned int)*8 == 32,
              "Unexpected size for unsigned int");

inline cvc4_uint32 left_rotate(cvc4_uint32 x, std::size_t n)
{
    return (x<<n) ^ (x>> (32-n));
}

class sha1
{
public:
    typedef cvc4_uint32(&digest_type)[5];
public:
    sha1(unsigned rounds = 80);

    void reset();

    void process_byte(cvc4_uchar8 byte);
    void process_block(void const* bytes_begin, void const* bytes_end);
    void process_bytes(void const* buffer, std::size_t byte_count);

    void get_digest(digest_type digest);

private:
    void process_block();

private:
    cvc4_uint32 h_[5];

    cvc4_uchar8 block_[64];

    std::size_t block_byte_index_;
    std::size_t byte_count_;

    unsigned rounds_;
};

inline sha1::sha1(unsigned rounds)
: rounds_(rounds)
{
    reset();
}

inline void sha1::reset()
{
    h_[0] = 0x67452301;
    h_[1] = 0xEFCDAB89;
    h_[2] = 0x98BADCFE;
    h_[3] = 0x10325476;
    h_[4] = 0xC3D2E1F0;

    block_byte_index_ = 0;
    byte_count_ = 0;
}

inline void sha1::process_byte(cvc4_uchar8 byte)
{
    block_[block_byte_index_++] = byte;
    ++byte_count_;
    if (block_byte_index_ == 64) {
        block_byte_index_ = 0;
        process_block();
    }
}

inline void sha1::process_block(void const* bytes_begin, void const* bytes_end)
{
    cvc4_uchar8 const* begin = static_cast<cvc4_uchar8 const*>(bytes_begin);
    cvc4_uchar8 const* end = static_cast<cvc4_uchar8 const*>(bytes_end);
    for(; begin != end; ++begin) {
        process_byte(*begin);
    }
}

inline void sha1::process_bytes(void const* buffer, std::size_t byte_count)
{
    cvc4_uchar8 const* b = static_cast<cvc4_uchar8 const*>(buffer);
    process_block(b, b+byte_count);
}

inline void sha1::process_block()
{
    cvc4_uint32 w[80];
    for (std::size_t i=0; i<16; ++i) {
        w[i]  = (block_[i*4 + 0] << 24);
        w[i] |= (block_[i*4 + 1] << 16);
        w[i] |= (block_[i*4 + 2] << 8);
        w[i] |= (block_[i*4 + 3]);
    }
    for (std::size_t i=16; i<80; ++i) {
        w[i] = left_rotate((w[i-3] ^ w[i-8] ^ w[i-14] ^ w[i-16]), 1);
    }

    cvc4_uint32 a = h_[0];
    cvc4_uint32 b = h_[1];
    cvc4_uint32 c = h_[2];
    cvc4_uint32 d = h_[3];
    cvc4_uint32 e = h_[4];

    for (std::size_t i=0; i<rounds_; ++i) {
        cvc4_uint32 f;
        cvc4_uint32 k;

        if (i<20) {
            f = (b & c) | (~b & d);
            k = 0x5A827999;
        } else if (i<40) {
            f = b ^ c ^ d;
            k = 0x6ED9EBA1;
        } else if (i<60) {
            f = (b & c) | (b & d) | (c & d);
            k = 0x8F1BBCDC;
        } else {
            f = b ^ c ^ d;
            k = 0xCA62C1D6;
        }

        cvc4_uint32 temp = left_rotate(a, 5) + f + e + k + w[i];
        e = d;
        d = c;
        c = left_rotate(b, 30);
        b = a;
        a = temp;
    }

    h_[0] += a;
    h_[1] += b;
    h_[2] += c;
    h_[3] += d;
    h_[4] += e;
}

inline void sha1::get_digest(digest_type digest)
{
    std::size_t bit_count = byte_count_*8;

    // append the bit '1' to the message
    process_byte(0x80);

    // append k bits '0', where k is the minimum number >= 0
    // such that the resulting message length is congruent to 56 (mod 64)
    // check if there is enough space for padding and bit_count
    if (block_byte_index_ > 56) {
        // finish this block
        while (block_byte_index_ != 0) {
            process_byte(0);
        }

        // one more block
        while (block_byte_index_ < 56) {
            process_byte(0);
        }
    } else {
        while (block_byte_index_ < 56) {
            process_byte(0);
        }
    }

    // append length of message (before pre-processing) 
    // as a 64-bit big-endian integer
    process_byte(0);
    process_byte(0);
    process_byte(0);
    process_byte(0);
    process_byte( static_cast<unsigned char>((bit_count>>24) & 0xFF));
    process_byte( static_cast<unsigned char>((bit_count>>16) & 0xFF));
    process_byte( static_cast<unsigned char>((bit_count>>8 ) & 0xFF));
    process_byte( static_cast<unsigned char>((bit_count)     & 0xFF));

    // get final digest
    digest[0] = h_[0];
    digest[1] = h_[1];
    digest[2] = h_[2];
    digest[3] = h_[3];
    digest[4] = h_[4];
}

} // namespace hashsmt

#endif /* __CVC4__EXAMPLES__HASHSMT__SHA1_H */
