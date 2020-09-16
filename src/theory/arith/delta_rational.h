/*********************                                                        */
/*! \file delta_rational.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Dejan Jovanovic, Morgan Deters
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

#include "cvc4_private.h"

#pragma once

#include <ostream>

#include "base/check.h"
#include "base/exception.h"
#include "util/integer.h"
#include "util/rational.h"

namespace CVC4 {

class DeltaRational;

class DeltaRationalException : public Exception {
 public:
  DeltaRationalException(const char* op,
                         const DeltaRational& a,
                         const DeltaRational& b);
  ~DeltaRationalException() override;
};


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
  DeltaRational() : c(0,1), k(0,1) {}
  DeltaRational(const CVC4::Rational& base) : c(base), k(0,1) {}
  DeltaRational(const CVC4::Rational& base, const CVC4::Rational& coeff) :
    c(base), k(coeff) {}

  const CVC4::Rational& getInfinitesimalPart() const {
    return k;
  }

  const CVC4::Rational& getNoninfinitesimalPart() const {
    return c;
  }

  int sgn() const {
    int s = getNoninfinitesimalPart().sgn();
    if(s == 0){
      return infinitesimalSgn();
    }else{
      return s;
    }
  }

  int infinitesimalSgn() const {
    return getInfinitesimalPart().sgn();
  }

  bool infinitesimalIsZero() const {
    return getInfinitesimalPart().isZero();
  }

  bool noninfinitesimalIsZero() const {
    return getNoninfinitesimalPart().isZero();
  }

  bool isZero() const {
    return noninfinitesimalIsZero() && infinitesimalIsZero();
  }


  int cmp(const DeltaRational& other) const{
    int cmp = c.cmp(other.c);
    if(cmp == 0){
      return k.cmp(other.k);
    }else{
      return cmp;
    }
  }

  DeltaRational operator+(const DeltaRational& other) const{
    CVC4::Rational tmpC = c+other.c;
    CVC4::Rational tmpK = k+other.k;
    return DeltaRational(tmpC, tmpK);
  }

  DeltaRational operator*(const Rational& a) const{
    CVC4::Rational tmpC = a*c;
    CVC4::Rational tmpK = a*k;
    return DeltaRational(tmpC, tmpK);
  }


  /**
   * Multiplies (this->c + this->k * delta) * (a.c + a.k * delta)
   * This can be done whenever this->k or a.k is 0.
   * Otherwise, the result is not a DeltaRational and a DeltaRationalException is thrown.
   */
  DeltaRational operator*(const DeltaRational& a) const
  /* throw(DeltaRationalException) */ {
    if(infinitesimalIsZero()){
      return a * (this->getNoninfinitesimalPart());
    }else if(a.infinitesimalIsZero()){
      return (*this) * a.getNoninfinitesimalPart();
    }else{
      throw DeltaRationalException("operator*", *this, a);
    }
  }


  DeltaRational operator-(const DeltaRational& a) const{
    CVC4::Rational negOne(CVC4::Integer(-1));
    return *(this) + (a * negOne);
  }

  DeltaRational operator-() const{
    return DeltaRational(-c, -k);
  }

  DeltaRational operator/(const Rational& a) const{
    CVC4::Rational tmpC = c/a;
    CVC4::Rational tmpK = k/a;
    return DeltaRational(tmpC, tmpK);
  }

  DeltaRational operator/(const Integer& a) const{
    CVC4::Rational tmpC = c/a;
    CVC4::Rational tmpK = k/a;
    return DeltaRational(tmpC, tmpK);
  }

  /**
   * Divides (*this) / (a.c + a.k * delta)
   * This can be done when a.k is 0 and a.c is non-zero.
   * Otherwise, the result is not a DeltaRational and a DeltaRationalException is thrown.
   */
  DeltaRational operator/(const DeltaRational& a) const
  /* throw(DeltaRationalException) */ {
    if(a.infinitesimalIsZero()){
      return (*this) / a.getNoninfinitesimalPart();
    }else{
      throw DeltaRationalException("operator/", *this, a);
    }
  }


  DeltaRational abs() const {
    if(sgn() >= 0){
      return *this;
    }else{
      return (*this) * Rational(-1);
    }
  }

  bool operator==(const DeltaRational& other) const{
    return (k == other.k) && (c == other.c);
  }

  bool operator!=(const DeltaRational& other) const{
    return !(*this == other);
  }


  bool operator<=(const DeltaRational& other) const{
    int cmp = c.cmp(other.c);
    return (cmp < 0) || ((cmp==0)&&(k <= other.k));
  }
  bool operator<(const DeltaRational& other) const{
    return (other  > *this);
  }
  bool operator>=(const DeltaRational& other) const{
    return (other <= *this);
  }
  bool operator>(const DeltaRational& other) const{
    return !(*this <= other);
  }

  int compare(const DeltaRational& other) const{
    int cmpRes = c.cmp(other.c);
    return (cmpRes != 0) ? cmpRes : (k.cmp(other.k));
  }

  DeltaRational& operator=(const DeltaRational& other){
    c = other.c;
    k = other.k;
    return *(this);
  }

  DeltaRational& operator*=(const CVC4::Rational& a){
    c *=  a;
    k *=  a;

    return *(this);
  }

  DeltaRational& operator+=(const DeltaRational& other){
    c += other.c;
    k += other.k;

    return *(this);
  }

  DeltaRational& operator/=(const Rational& a){
    Assert(!a.isZero());
    c /= a;
    k /= a;
    return *(this);
  }

  bool isIntegral() const {
    if(infinitesimalIsZero()){
      return getNoninfinitesimalPart().isIntegral();
    }else{
      return false;
    }
  }

  Integer floor() const {
    if(getNoninfinitesimalPart().isIntegral()){
      if(getInfinitesimalPart().sgn() >= 0){
        return getNoninfinitesimalPart().getNumerator();
      }else{
        return getNoninfinitesimalPart().getNumerator() - Integer(1);
      }
    }else{
      return getNoninfinitesimalPart().floor();
    }
  }

  Integer ceiling() const {
    if(getNoninfinitesimalPart().isIntegral()){
      if(getInfinitesimalPart().sgn() <= 0){
        return getNoninfinitesimalPart().getNumerator();
      }else{
        return getNoninfinitesimalPart().getNumerator() + Integer(1);
      }
    }else{
      return getNoninfinitesimalPart().ceiling();
    }
  }

  /** Only well defined if both this and y are integral. */
  Integer euclidianDivideQuotient(const DeltaRational& y) const
      /* throw(DeltaRationalException) */;

  /** Only well defined if both this and y are integral. */
  Integer euclidianDivideRemainder(const DeltaRational& y) const
      /* throw(DeltaRationalException) */;

  std::string toString() const;

  Rational substituteDelta(const Rational& d) const{
    return getNoninfinitesimalPart() + (d * getInfinitesimalPart());
  }

  /**
   * Computes a sufficient upperbound to separate two DeltaRationals.
   * This value is stored in res.
   * For any rational d such that
   *   0 < d < res
   * then
   *   a < b if and only if substituteDelta(a, d) < substituteDelta(b,d).
   * (Similar relationships hold for for a == b and a > b.)
   * Precondition: res > 0
   */
  static void seperatingDelta(Rational& res, const DeltaRational& a, const DeltaRational& b);

  uint32_t complexity() const {
    return c.complexity() + k.complexity();
  }

  double approx(double deltaSub) const {
    double maj = getNoninfinitesimalPart().getDouble();
    double min = deltaSub * (getInfinitesimalPart().getDouble());
    return maj + min;
  }


};

std::ostream& operator<<(std::ostream& os, const DeltaRational& n);

}/* CVC4 namespace */
