#ifndef sc2__position_h
#define sc2__position_h

#include <iostream>
#include <stdio.h>

class Position {
public:
  const char *filename;
  int linenum; 
  int colnum;

  Position(const char *_f, int l, int c) : filename(_f), linenum(l), colnum(c)
  {}
  void print(std::ostream &os) {
    os << filename;
    if (colnum == -1) {
      char tmp[1024];
      sprintf(tmp, ", line %d, end of column: ", linenum);
      os << tmp;
    }
    else {
      char tmp[1024];
      sprintf(tmp, ", line %d, column %d: ", linenum, colnum);
      os << tmp;
    }
  }
};

#endif
