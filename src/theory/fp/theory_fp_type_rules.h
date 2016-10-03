/*********************                                                        */
/*! \file theory_fp_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__FP__THEORY_FP_TYPE_RULES_H
#define __CVC4__THEORY__FP__THEORY_FP_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace fp {

#define TRACE(FUNCTION)                                                \
  Trace("fp-type") << FUNCTION "::computeType(" << check << "): " << n \
                   << std::endl

class FloatingPointConstantTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointConstantTypeRule");

    const FloatingPoint& f = n.getConst<FloatingPoint>();

    if (check) {
      if (!(validExponentSize(f.t.exponent()))) {
        throw TypeCheckingExceptionPrivate(
            n, "constant with invalid exponent size");
      }
      if (!(validSignificandSize(f.t.significand()))) {
        throw TypeCheckingExceptionPrivate(
            n, "constant with invalid significand size");
      }
    }
    return nodeManager->mkFloatingPointType(f.t);
  }
};

class RoundingModeConstantTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("RoundingModeConstantTypeRule");

    // Nothing to check!
    return nodeManager->roundingModeType();
  }
};

class FloatingPointFPTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointFPTypeRule");

    TypeNode signType = n[0].getType(check);
    TypeNode exponentType = n[1].getType(check);
    TypeNode significandType = n[2].getType(check);

    if (!signType.isBitVector() || !exponentType.isBitVector() ||
        !significandType.isBitVector()) {
      throw TypeCheckingExceptionPrivate(n,
                                         "arguments to fp must be bit vectors");
    }

    unsigned signBits = signType.getBitVectorSize();
    unsigned exponentBits = exponentType.getBitVectorSize();
    unsigned significandBits = significandType.getBitVectorSize();

    if (check) {
      if (signBits != 1) {
        throw TypeCheckingExceptionPrivate(
            n, "sign bit vector in fp must be 1 bit long");
      } else if (!(validExponentSize(exponentBits))) {
        throw TypeCheckingExceptionPrivate(
            n, "exponent bit vector in fp is an invalid size");
      } else if (!(validSignificandSize(significandBits))) {
        throw TypeCheckingExceptionPrivate(
            n, "significand bit vector in fp is an invalid size");
      }
    }

    // The +1 is for the implicit hidden bit
    return nodeManager->mkFloatingPointType(exponentBits, significandBits + 1);
  }
};

class FloatingPointTestTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointTestTypeRule");

    if (check) {
      TypeNode firstOperand = n[0].getType(check);

      if (!firstOperand.isFloatingPoint()) {
        throw TypeCheckingExceptionPrivate(
            n, "floating-point test applied to a non floating-point sort");
      }

      size_t children = n.getNumChildren();
      for (size_t i = 1; i < children; ++i) {
        if (!(n[i].getType(check) == firstOperand)) {
          throw TypeCheckingExceptionPrivate(
              n, "floating-point test applied to mixed sorts");
        }
      }
    }

    return nodeManager->booleanType();
  }
};

class FloatingPointOperationTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointOperationTypeRule");

    TypeNode firstOperand = n[0].getType(check);

    if (check) {
      if (!firstOperand.isFloatingPoint()) {
        throw TypeCheckingExceptionPrivate(
            n, "floating-point operation applied to a non floating-point sort");
      }

      size_t children = n.getNumChildren();
      for (size_t i = 1; i < children; ++i) {
        if (!(n[i].getType(check) == firstOperand)) {
          throw TypeCheckingExceptionPrivate(
              n, "floating-point test applied to mixed sorts");
        }
      }
    }

    return firstOperand;
  }
};

class FloatingPointRoundingOperationTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointRoundingOperationTypeRule");

    if (check) {
      TypeNode roundingModeType = n[0].getType(check);

      if (!roundingModeType.isRoundingMode()) {
        throw TypeCheckingExceptionPrivate(
            n, "first argument must be a rounding mode");
      }
    }

    TypeNode firstOperand = n[1].getType(check);

    if (check) {
      if (!firstOperand.isFloatingPoint()) {
        throw TypeCheckingExceptionPrivate(
            n, "floating-point operation applied to a non floating-point sort");
      }

      size_t children = n.getNumChildren();
      for (size_t i = 2; i < children; ++i) {
        if (!(n[i].getType(check) == firstOperand)) {
          throw TypeCheckingExceptionPrivate(
              n, "floating-point test applied to mixed sorts");
        }
      }
    }

    return firstOperand;
  }
};

class FloatingPointParametricOpTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointParametricOpTypeRule");

    return nodeManager->builtinOperatorType();
  }
};

class FloatingPointToFPIEEEBitVectorTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointToFPIEEEBitVectorTypeRule");

    FloatingPointToFPIEEEBitVector info =
        n.getOperator().getConst<FloatingPointToFPIEEEBitVector>();

    if (check) {
      TypeNode operandType = n[0].getType(check);

      if (!(operandType.isBitVector())) {
        throw TypeCheckingExceptionPrivate(n,
                                           "conversion to floating-point from "
                                           "bit vector used with sort other "
                                           "than bit vector");
      } else if (!(operandType.getBitVectorSize() ==
                   info.t.exponent() + info.t.significand())) {
        throw TypeCheckingExceptionPrivate(
            n,
            "conversion to floating-point from bit vector used with bit vector "
            "length that does not match floating point parameters");
      }
    }

    return nodeManager->mkFloatingPointType(info.t);
  }
};

class FloatingPointToFPFloatingPointTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointToFPFloatingPointTypeRule");

    FloatingPointToFPFloatingPoint info =
        n.getOperator().getConst<FloatingPointToFPFloatingPoint>();

    if (check) {
      TypeNode roundingModeType = n[0].getType(check);

      if (!roundingModeType.isRoundingMode()) {
        throw TypeCheckingExceptionPrivate(
            n, "first argument must be a rounding mode");
      }

      TypeNode operandType = n[1].getType(check);

      if (!(operandType.isFloatingPoint())) {
        throw TypeCheckingExceptionPrivate(n,
                                           "conversion to floating-point from "
                                           "floating-point used with sort "
                                           "other than floating-point");
      }
    }

    return nodeManager->mkFloatingPointType(info.t);
  }
};

class FloatingPointToFPRealTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointToFPRealTypeRule");

    FloatingPointToFPReal info =
        n.getOperator().getConst<FloatingPointToFPReal>();

    if (check) {
      TypeNode roundingModeType = n[0].getType(check);

      if (!roundingModeType.isRoundingMode()) {
        throw TypeCheckingExceptionPrivate(
            n, "first argument must be a rounding mode");
      }

      TypeNode operandType = n[1].getType(check);

      if (!(operandType.isReal())) {
        throw TypeCheckingExceptionPrivate(n,
                                           "conversion to floating-point from "
                                           "real used with sort other than "
                                           "real");
      }
    }

    return nodeManager->mkFloatingPointType(info.t);
  }
};

class FloatingPointToFPSignedBitVectorTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointToFPSignedBitVectorTypeRule");

    FloatingPointToFPSignedBitVector info =
        n.getOperator().getConst<FloatingPointToFPSignedBitVector>();

    if (check) {
      TypeNode roundingModeType = n[0].getType(check);

      if (!roundingModeType.isRoundingMode()) {
        throw TypeCheckingExceptionPrivate(
            n, "first argument must be a rounding mode");
      }

      TypeNode operandType = n[1].getType(check);

      if (!(operandType.isBitVector())) {
        throw TypeCheckingExceptionPrivate(n,
                                           "conversion to floating-point from "
                                           "signed bit vector used with sort "
                                           "other than bit vector");
      }
    }

    return nodeManager->mkFloatingPointType(info.t);
  }
};

class FloatingPointToFPUnsignedBitVectorTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointToFPUnsignedBitVectorTypeRule");

    FloatingPointToFPUnsignedBitVector info =
        n.getOperator().getConst<FloatingPointToFPUnsignedBitVector>();

    if (check) {
      TypeNode roundingModeType = n[0].getType(check);

      if (!roundingModeType.isRoundingMode()) {
        throw TypeCheckingExceptionPrivate(
            n, "first argument must be a rounding mode");
      }

      TypeNode operandType = n[1].getType(check);

      if (!(operandType.isBitVector())) {
        throw TypeCheckingExceptionPrivate(n,
                                           "conversion to floating-point from "
                                           "unsigned bit vector used with sort "
                                           "other than bit vector");
      }
    }

    return nodeManager->mkFloatingPointType(info.t);
  }
};

class FloatingPointToFPGenericTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointToFPGenericTypeRule");

    FloatingPointToFPGeneric info =
        n.getOperator().getConst<FloatingPointToFPGeneric>();

    if (check) {
      /* As this is a generic kind intended only for parsing,
       * the checking here is light.  For better checking, use
       * expandDefinitions first.
       */

      size_t children = n.getNumChildren();
      for (size_t i = 0; i < children; ++i) {
        n[i].getType(check);
      }
    }

    return nodeManager->mkFloatingPointType(info.t);
  }
};

class FloatingPointToUBVTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointToUBVTypeRule");

    FloatingPointToUBV info = n.getOperator().getConst<FloatingPointToUBV>();

    if (check) {
      TypeNode roundingModeType = n[0].getType(check);

      if (!roundingModeType.isRoundingMode()) {
        throw TypeCheckingExceptionPrivate(
            n, "first argument must be a rounding mode");
      }

      TypeNode operandType = n[1].getType(check);

      if (!(operandType.isFloatingPoint())) {
        throw TypeCheckingExceptionPrivate(n,
                                           "conversion to unsigned bit vector "
                                           "used with a sort other than "
                                           "floating-point");
      }
    }

    return nodeManager->mkBitVectorType(info.bvs);
  }
};

class FloatingPointToSBVTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointToSBVTypeRule");

    FloatingPointToSBV info = n.getOperator().getConst<FloatingPointToSBV>();

    if (check) {
      TypeNode roundingModeType = n[0].getType(check);

      if (!roundingModeType.isRoundingMode()) {
        throw TypeCheckingExceptionPrivate(
            n, "first argument must be a rounding mode");
      }

      TypeNode operandType = n[1].getType(check);

      if (!(operandType.isFloatingPoint())) {
        throw TypeCheckingExceptionPrivate(n,
                                           "conversion to signed bit vector "
                                           "used with a sort other than "
                                           "floating-point");
      }
    }

    return nodeManager->mkBitVectorType(info.bvs);
  }
};

class FloatingPointToRealTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    TRACE("FloatingPointToRealTypeRule");

    if (check) {
      TypeNode roundingModeType = n[0].getType(check);

      if (!roundingModeType.isRoundingMode()) {
        throw TypeCheckingExceptionPrivate(
            n, "first argument must be a rounding mode");
      }

      TypeNode operand = n[1].getType(check);

      if (!operand.isFloatingPoint()) {
        throw TypeCheckingExceptionPrivate(
            n, "floating-point to real applied to a non floating-point sort");
      }
    }

    return nodeManager->realType();
  }
};

} /* CVC4::theory::fp namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__FP__THEORY_FP_TYPE_RULES_H */
