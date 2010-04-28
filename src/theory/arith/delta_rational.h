#include "cvc4_private.h"

#include "util/integer.h"
#include "util/rational.h"


#ifndef __CVC4__THEORY__ARITH__DELTA_RATIONAL_H
#define __CVC4__THEORY__ARITH__DELTA_RATIONAL_H

/**
 * A DeltaRational is a pair of rationals (c,k) that represent the number
 *   c + kd
 * where d is an implicit system wide symbolic infinitesimal.
 */
class DeltaRational {
private:
  CVC4::Rational c;
  CVC4::Rational k;

public:
  DeltaRational() : c(0), k(0) {}
  DeltaRational(const CVC4::Rational& base) : c(base), k(0) {}
  DeltaRational(const CVC4::Rational& base, const CVC4::Rational& coeff) :
    c(base), k(coeff) {}

  DeltaRational operator+(const DeltaRational& other) const{
    CVC4::Rational tmpC = c+other.c;
    CVC4::Rational tmpK = k+other.k;
    return DeltaRational(tmpC, tmpK);
  }

  DeltaRational operator*(CVC4::Rational& a) const{
    CVC4::Rational tmpC = a*c;
    CVC4::Rational tmpK = a*k;
    return DeltaRational(tmpC, tmpK);
  }

  DeltaRational operator-(const DeltaRational& a) const{
    CVC4::Rational negOne(CVC4::Integer(-1));
    return *(this) + (a * negOne);
  }

  bool operator==(DeltaRational& other){
    return (k == other.k) && (c == other.c);
  }

  bool operator<=(DeltaRational& other){
    int cmp = c.cmp(other.c);
    return (cmp < 0) || ((cmp==0)&&(k <= other.k));
  }
  bool operator<(DeltaRational& other){
    return (other  > *this);
  }
  bool operator>=(DeltaRational& other){
    return (other <= *this);
  }
  bool operator>(DeltaRational& other){
    return !(*this <= other);
  }

  DeltaRational& operator=(DeltaRational& other){
    c = other.c;
    k = other.k;
    return *(this);
  }

  DeltaRational& operator*=(CVC4::Rational& a){
    c = c * a;
    k = k * a;

    return *(this);
  }

  DeltaRational& operator+=(DeltaRational& other){
    c =c + other.c;
    k =k + other.k;

    return *(this);
  }
};

#endif /* __CVC4__THEORY__ARITH__DELTA_RATIONAL_H */
