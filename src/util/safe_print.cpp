/*********************                                                        */
/*! \file safe_print.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Definition of print functions that are safe to use in a signal
 ** handler.
 **
 ** Signal handlers only allow a very limited set of operations, e.g. dynamic
 ** memory allocation is not possible. This set of functions can be used to
 ** print information from a signal handler. All output is written to file
 ** descriptors using the async-signal-safe write() function.
 **/

#include "safe_print.h"

#include <unistd.h>

/* Size of buffers used */
#define BUFFER_SIZE 20

namespace CVC4 {

template <>
void safe_print(int fd, const std::string& msg) {
  // Print characters one by one instead of using
  // string::data()/string::c_str() to avoid allocations (pre-c++11)
  for (size_t i = 0; i < msg.length(); i++) {
    if (write(fd, &(msg[i]), 1) != 1) {
      abort();
    }
  }
}

template <>
void safe_print(int fd, const int64_t& _i) {
  char buf[BUFFER_SIZE];
  int64_t i = _i;

  if (i == 0) {
    safe_print(fd, "0");
    return;
  } else if (i < 0) {
    safe_print(fd, "-");
    i *= -1;
  }

  // This loop fills the buffer from the end. The number of elements in the
  // buffer is BUFER_SIZE - idx - 1 and they start at position idx + 1.
  ssize_t idx = BUFFER_SIZE - 1;
  while (i != 0 && idx >= 0) {
    buf[idx] = '0' + i % 10;
    i /= 10;
    idx--;
  }

  ssize_t nbyte = BUFFER_SIZE - idx - 1;
  if (write(fd, buf + idx + 1, nbyte) != nbyte) {
    abort();
  }
}

template <>
void safe_print(int fd, const int32_t& i) {
  safe_print<int64_t>(fd, i);
}

template <>
void safe_print(int fd, const uint64_t& _i) {
  char buf[BUFFER_SIZE];
  uint64_t i = _i;

  if (i == 0) {
    safe_print(fd, "0");
    return;
  }

  // This loop fills the buffer from the end. The number of elements in the
  // buffer is BUFER_SIZE - idx - 1 and they start at position idx + 1.
  ssize_t idx = BUFFER_SIZE - 1;
  while (i != 0 && idx >= 0) {
    buf[idx] = '0' + i % 10;
    i /= 10;
    idx--;
  }

  ssize_t nbyte = BUFFER_SIZE - idx - 1;
  if (write(fd, buf + idx + 1, nbyte) != nbyte) {
    abort();
  }
}

template <>
void safe_print(int fd, const uint32_t& i) {
  safe_print<uint64_t>(fd, i);
}

template <>
void safe_print(int fd, const double& _d) {
  // Note: this print function for floating-point values is optimized for
  // simplicity, not correctness or performance.
  char buf[BUFFER_SIZE];
  double d = _d;

  ssize_t i = 0;
  int64_t v = static_cast<int64_t>(d);
  d -= v;

  if (d < 0.0) {
    d *= -1.0;
  }

  safe_print<int64_t>(fd, v);
  safe_print(fd, ".");

  // Print decimal digits as long as the remaining value is larger than zero
  // and print at least one digit.
  while (i == 0 || (d > 0.0 && i < BUFFER_SIZE)) {
    d *= 10.0;
    char c = static_cast<char>(d);
    buf[i] = '0' + c;
    d -= c;
    i++;
  }

  if (write(fd, buf, i) != i) {
    abort();
  }
}

template <>
void safe_print(int fd, const float& f) {
  safe_print<double>(fd, (double)f);
}

template <>
void safe_print(int fd, const bool& b) {
  if (b) {
    safe_print(fd, "true");
  } else {
    safe_print(fd, "false");
  }
}

template <>
void safe_print(int fd, void* const& addr) {
  safe_print_hex(fd, (uint64_t)addr);
}

template <>
void safe_print(int fd, const timespec& t) {
  safe_print<uint64_t>(fd, t.tv_sec);
  safe_print(fd, ".");
  safe_print_right_aligned(fd, t.tv_nsec, 9);
}

void safe_print_hex(int fd, uint64_t i) {
  char buf[BUFFER_SIZE];

  safe_print(fd, "0x");
  if (i == 0) {
    safe_print(fd, "0");
    return;
  }

  // This loop fills the buffer from the end. The number of elements in the
  // buffer is BUFER_SIZE - idx - 1 and they start at position idx + 1.
  ssize_t idx = BUFFER_SIZE - 1;
  while (i != 0 && idx >= 0) {
    char current = i % 16;
    if (current <= 9) {
      buf[idx] = '0' + current;
    } else {
      buf[idx] = 'a' + current - 10;
    }
    i /= 16;
    idx--;
  }

  ssize_t nbyte = BUFFER_SIZE - idx - 1;
  if (write(fd, buf + idx + 1, nbyte) != nbyte) {
    abort();
  }
}

void safe_print_right_aligned(int fd, uint64_t i, ssize_t width) {
  char buf[BUFFER_SIZE];

  // Make sure that the result fits in the buffer
  width = (width < BUFFER_SIZE) ? width : BUFFER_SIZE;

  for (ssize_t j = 0; j < width; j++) {
    buf[j] = '0';
  }

  ssize_t idx = width - 1;
  while (i != 0 && idx >= 0) {
    buf[idx] = '0' + i % 10;
    i /= 10;
    idx--;
  }

  if (write(fd, buf, width) != width) {
    abort();
  }
}

} /* CVC4 namespace */
