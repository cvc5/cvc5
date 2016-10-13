/*********************                                                        */
/*! \file floatingpoint.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Tim King
 ** Copyright (c) 2013  University of Oxford
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Utility functions for working with floating point theories. ]]
 **
 ** [[ This file contains the data structures used by the constant and
 **    parametric types of the floating point theory. ]]
 **/
#include "cvc4_public.h"

#ifndef __CVC4__FLOATINGPOINT_H
#define __CVC4__FLOATINGPOINT_H

#include <fenv.h>

#include "util/bitvector.h"

namespace CVC4 {
  // Inline these!
  inline bool CVC4_PUBLIC validExponentSize (unsigned e) { return e >= 2; }
  inline bool CVC4_PUBLIC validSignificandSize (unsigned s) { return s >= 2; }

  /**
   * Floating point sorts are parameterised by two non-zero constants
   * giving the width (in bits) of the exponent and significand
   * (including the hidden bit).
   */
  class CVC4_PUBLIC FloatingPointSize {
    /*
      Class invariants:
      * VALIDEXPONENTSIZE(e)
      * VALIDSIGNIFCANDSIZE(s)
     */

  private :
    unsigned e;
    unsigned s;

  public :
    FloatingPointSize (unsigned _e, unsigned _s);
    FloatingPointSize (const FloatingPointSize &old);

    inline unsigned exponent (void) const {
      return this->e;
    }

    inline unsigned significand (void) const {
      return this->s;
    }

    bool operator ==(const FloatingPointSize& fps) const {
      return (e == fps.e) && (s == fps.s);
    }

  }; /* class FloatingPointSize */

  struct CVC4_PUBLIC FloatingPointSizeHashFunction {
    static inline size_t ROLL(size_t X, size_t N) {
      return (((X) << (N)) | ((X) >> (8*sizeof((X)) - (N)) ));
    }

    inline size_t operator() (const FloatingPointSize& fpt) const {
      return size_t(ROLL(fpt.exponent(), 4*sizeof(unsigned)) |
		    fpt.significand());
    }
  }; /* struct FloatingPointSizeHashFunction */


  /**
   * A concrete instance of the rounding mode sort
   */
  enum CVC4_PUBLIC RoundingMode {
    roundNearestTiesToEven = FE_TONEAREST,
    roundTowardPositive = FE_UPWARD,
    roundTowardNegative = FE_DOWNWARD,
    roundTowardZero = FE_TOWARDZERO,
    // Initializes this to the diagonalization of the 4 other values.
    roundNearestTiesToAway = (((~FE_TONEAREST) & 0x1) | ((~FE_UPWARD) & 0x2) |
                              ((~FE_DOWNWARD) & 0x4) | ((~FE_TOWARDZERO) & 0x8))
  }; /* enum RoundingMode */

  struct CVC4_PUBLIC RoundingModeHashFunction {
    inline size_t operator() (const RoundingMode& rm) const {
      return size_t(rm);
    }
  }; /* struct RoundingModeHashFunction */


  /**
   * A concrete floating point number
   */

  class CVC4_PUBLIC FloatingPointLiteral {
  public :
    // This intentional left unfinished as the choice of literal
    // representation is solver specific.
    void unfinished (void) const;

    FloatingPointLiteral(unsigned, unsigned, double) { unfinished(); }
    FloatingPointLiteral(unsigned, unsigned, const std::string &) { unfinished(); }
    FloatingPointLiteral(const FloatingPointLiteral &) { unfinished(); }

    bool operator == (const FloatingPointLiteral &op) const {
      unfinished();
      return false;
    }

    size_t hash (void) const {
      unfinished();
      return 23;
    }
  };

  class CVC4_PUBLIC FloatingPoint {
  protected :
    FloatingPointLiteral fpl;

  public :
    FloatingPointSize t;

    FloatingPoint (unsigned e, unsigned s, double d) : fpl(e,s,d), t(e,s) {}
    FloatingPoint (unsigned e, unsigned s, const std::string &bitString) : fpl(e,s,bitString), t(e,s) {}
    FloatingPoint (const FloatingPoint &fp) : fpl(fp.fpl), t(fp.t) {}

    bool operator ==(const FloatingPoint& fp) const {
      return ( (t == fp.t) && fpl == fp.fpl );
    }

    const FloatingPointLiteral & getLiteral (void) const {
      return this->fpl;
    }

  }; /* class FloatingPoint */


  struct CVC4_PUBLIC FloatingPointHashFunction {
    inline size_t operator() (const FloatingPoint& fp) const {
      FloatingPointSizeHashFunction h;
      return h(fp.t) ^ fp.getLiteral().hash();
    }
  }; /* struct FloatingPointHashFunction */

  /**
   * The parameter type for the conversions to floating point.
   */
  class CVC4_PUBLIC FloatingPointConvertSort {
  public :
    FloatingPointSize t;

    FloatingPointConvertSort (unsigned _e, unsigned _s)
      : t(_e,_s) {}

    bool operator ==(const FloatingPointConvertSort& fpcs) const {
      return t == fpcs.t;
    }

  };

  /**
   * As different conversions are different parameterised kinds, there
   * is a need for different (C++) types for each one.
   */

  class CVC4_PUBLIC FloatingPointToFPIEEEBitVector : public FloatingPointConvertSort {
  public : FloatingPointToFPIEEEBitVector (unsigned _e, unsigned _s) : FloatingPointConvertSort(_e,_s) {}
  };
  class CVC4_PUBLIC FloatingPointToFPFloatingPoint : public FloatingPointConvertSort {
  public : FloatingPointToFPFloatingPoint (unsigned _e, unsigned _s) : FloatingPointConvertSort(_e,_s) {}
  };
  class CVC4_PUBLIC FloatingPointToFPReal : public FloatingPointConvertSort {
  public : FloatingPointToFPReal (unsigned _e, unsigned _s) : FloatingPointConvertSort(_e,_s) {}
  };
  class CVC4_PUBLIC FloatingPointToFPSignedBitVector : public FloatingPointConvertSort {
  public : FloatingPointToFPSignedBitVector (unsigned _e, unsigned _s) : FloatingPointConvertSort(_e,_s) {}
  };
  class CVC4_PUBLIC FloatingPointToFPUnsignedBitVector : public FloatingPointConvertSort {
  public : FloatingPointToFPUnsignedBitVector (unsigned _e, unsigned _s) : FloatingPointConvertSort(_e,_s) {}
  };
  class CVC4_PUBLIC FloatingPointToFPGeneric : public FloatingPointConvertSort {
  public : FloatingPointToFPGeneric (unsigned _e, unsigned _s) : FloatingPointConvertSort(_e,_s) {}
  };



  template <unsigned key>
  struct CVC4_PUBLIC FloatingPointConvertSortHashFunction {
    inline size_t operator() (const FloatingPointConvertSort& fpcs) const {
      FloatingPointSizeHashFunction f;
      return f(fpcs.t) ^ (0x00005300 | (key << 24));
    }
  }; /* struct FloatingPointConvertSortHashFunction */








  /**
   * The parameter type for the conversion to bit vector.
   */
  class CVC4_PUBLIC FloatingPointToBV {
  public :
    BitVectorSize bvs;

    FloatingPointToBV (unsigned s)
      : bvs(s) {}
    operator unsigned () const { return bvs; }
  };

  class CVC4_PUBLIC FloatingPointToUBV : public FloatingPointToBV {
  public : FloatingPointToUBV (unsigned _s) : FloatingPointToBV(_s) {}
  };
  class CVC4_PUBLIC FloatingPointToSBV : public FloatingPointToBV {
  public : FloatingPointToSBV (unsigned _s) : FloatingPointToBV(_s) {}
  };


  template <unsigned key>
  struct CVC4_PUBLIC FloatingPointToBVHashFunction {
    inline size_t operator() (const FloatingPointToBV& fptbv) const {
      UnsignedHashFunction< ::CVC4::BitVectorSize > f;
      return 	(key ^ 0x46504256) ^ f(fptbv.bvs);
    }
  }; /* struct FloatingPointToBVHashFunction */



  inline std::ostream& operator <<(std::ostream& os, const FloatingPointLiteral& fp) CVC4_PUBLIC;
  inline std::ostream& operator <<(std::ostream& os, const FloatingPointLiteral& fp) {
    fp.unfinished();
    return os;
  }

  inline std::ostream& operator <<(std::ostream& os, const FloatingPoint& fp) CVC4_PUBLIC;
  inline std::ostream& operator <<(std::ostream& os, const FloatingPoint& fp) {
    return os << fp.getLiteral();
  }

  inline std::ostream& operator <<(std::ostream& os, const FloatingPointSize& fps) CVC4_PUBLIC;
  inline std::ostream& operator <<(std::ostream& os, const FloatingPointSize& fps) {
    return os << "(_ FloatingPoint " << fps.exponent() << " " << fps.significand() << ")";
  }

  inline std::ostream& operator <<(std::ostream& os, const FloatingPointConvertSort& fpcs) CVC4_PUBLIC;
  inline std::ostream& operator <<(std::ostream& os, const FloatingPointConvertSort& fpcs) {
    return os << "(_ to_fp " << fpcs.t.exponent() << " " << fpcs.t.significand() << ")";
  }

}/* CVC4 namespace */

#endif /* __CVC4__FLOATINGPOINT_H */
