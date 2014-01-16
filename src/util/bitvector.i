%{
#include "util/bitvector.h"
%}

%ignore CVC4::BitVector::BitVector(unsigned, unsigned);

%rename(assign) CVC4::BitVector::operator=(const BitVector&);
%rename(equals) CVC4::BitVector::operator==(const BitVector&) const;
%ignore CVC4::BitVector::operator!=(const BitVector&) const;
%rename(plus) CVC4::BitVector::operator+(const BitVector&) const;
%rename(minus) CVC4::BitVector::operator-(const BitVector&) const;
%rename(minus) CVC4::BitVector::operator-() const;
%rename(times) CVC4::BitVector::operator*(const BitVector&) const;
%rename(bitXor) CVC4::BitVector::operator^(const BitVector&) const;
%rename(bitOr) CVC4::BitVector::operator|(const BitVector&) const;
%rename(bitAnd) CVC4::BitVector::operator&(const BitVector&) const;
%rename(complement) CVC4::BitVector::operator~() const;
%rename(less) CVC4::BitVector::operator<(const BitVector&) const;
%rename(lessEqual) CVC4::BitVector::operator<=(const BitVector&) const;
%rename(greater) CVC4::BitVector::operator>(const BitVector&) const;
%rename(greaterEqual) CVC4::BitVector::operator>=(const BitVector&) const;

%rename(equals) CVC4::BitVectorExtract::operator==(const BitVectorExtract&) const;
%rename(equals) CVC4::BitVectorBitOf::operator==(const BitVectorBitOf&) const;

%rename(toUnsigned) CVC4::BitVectorSize::operator unsigned() const;
%rename(toUnsigned) CVC4::BitVectorRepeat::operator unsigned() const;
%rename(toUnsigned) CVC4::BitVectorZeroExtend::operator unsigned() const;
%rename(toUnsigned) CVC4::BitVectorSignExtend::operator unsigned() const;
%rename(toUnsigned) CVC4::BitVectorRotateLeft::operator unsigned() const;
%rename(toUnsigned) CVC4::BitVectorRotateRight::operator unsigned() const;
%rename(toUnsigned) CVC4::IntToBitVector::operator unsigned() const;

%rename(apply) CVC4::BitVectorHashFunction::operator()(const BitVector&) const;
%rename(apply) CVC4::BitVectorExtractHashFunction::operator()(const BitVectorExtract&) const;
%rename(apply) CVC4::BitVectorBitOfHashFunction::operator()(const BitVectorBitOf&) const;

%ignore CVC4::operator<<(std::ostream&, const BitVector&);
%ignore CVC4::operator<<(std::ostream&, const BitVectorExtract&);
%ignore CVC4::operator<<(std::ostream&, const BitVectorBitOf&);
%ignore CVC4::operator<<(std::ostream&, const IntToBitVector&);

%include "util/bitvector.h"
