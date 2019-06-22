%{
#include "util/floatingpoint.h"
%}

// Ignore the methods related to FloatingPointLiteral (otherwise we have to
// wrap those classes as well)
%ignore CVC4::FloatingPointLiteral;
%ignore CVC4::FloatingPoint::FloatingPoint (const FloatingPointSize &oldt, const FloatingPointLiteral &oldfpl);
%ignore CVC4::FloatingPoint::getLiteral () const;

// Ignore the partial methods (otherwise we have to provide a template
// instantiation for std::pair<FloatingPoint, bool> which is quite ugly)
%ignore CVC4::FloatingPoint::max(const FloatingPoint &arg) const;
%ignore CVC4::FloatingPoint::min(const FloatingPoint &arg) const;
%ignore CVC4::FloatingPoint::convertToRational() const;
%ignore CVC4::FloatingPoint::convertToBV(BitVectorSize width, const RoundingMode &rm, bool signedBV) const;

%include "util/floatingpoint.h"
