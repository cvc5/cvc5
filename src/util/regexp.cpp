/*********************                                                        */
/*! \file regexp.cpp
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "util/regexp.h"
#include <iostream>

using namespace std;

namespace CVC4 {

std::string String::toString() const {
	std::string str;
	for(unsigned int i=0; i<d_str.size(); ++i) {
	  char c = convertUnsignedIntToChar( d_str[i] );
	  if(isprint( c )) {
		if(c == '\\') {
			str += "\\\\";
		} else if(c == '\"') {
			str += "\\\"";
		} else {
			str += c;
		}
	  } else {
		  std::string s;
		  switch(c) {
			case '\a': s = "\\a"; break;
			case '\b': s = "\\b"; break;
			case '\t': s = "\\t"; break;
			case '\r': s = "\\r"; break;
			case '\v': s = "\\v"; break;
			case '\f': s = "\\f"; break;
			case '\n': s = "\\n"; break;
			case '\e': s = "\\e"; break;
			default  : {
				std::string s2 = static_cast<std::ostringstream*>( &(std::ostringstream() << (int)c) )->str();
				if(s2.size() == 1) {
					s2 = "0" + s2;
				}
				s = "\\x" + s2;
			}
		  }
		  str += s;
	  }
	}
	return str;
}

std::ostream& operator <<(std::ostream& os, const String& s) {
  return os << "\"" << s.toString() << "\"";
}

std::ostream& operator<<(std::ostream& out, const RegExp& s) {
  return out << "regexp(" << s.getType() << ')';
}

}/* CVC4 namespace */