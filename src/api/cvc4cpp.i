%{
#include "api/cvc4cpp.h"
%}

namespace CVC4 {
  namespace api {
    %ignore operator<<(std::ostream&, const Result&);
    %ignore operator<<(std::ostream&, const Sort&);
    %ignore operator<<(std::ostream&, const Term&);
    %ignore operator<<(std::ostream&, const std::vector<Term>&);
    %ignore operator<<(std::ostream&, const std::set<Term>&);
    %ignore operator<<(std::ostream&, const std::unordered_set<Term, TermHashFunction>&);
    %ignore operator<<(std::ostream&, const OpTerm&);
  }
}

%rename(ApiResult) CVC4::api::Result;
%rename(ApiDatatype) CVC4::api::Datatype;
%rename(ApiDatatypeConstructor) CVC4::api::DatatypeConstructor;
%include "api/cvc4cpp.h"
/*
namespace CVC4 {
  namespace api {
    %ignore operator<<(std::ostream&, const Result&);
    %ignore operator<<(std::ostream&, const Sort&);
    %ignore operator<<(std::ostream&, const Term&);
    %ignore operator<<(std::ostream&, const std::vector<Term>&);
    %ignore operator<<(std::ostream&, const std::set<Term>&);
    %ignore operator<<(std::ostream&, const std::unordered_set<Term, TermHashFunction>&);
    %ignore operator<<(std::ostream&, const OpTerm&);

    class ApiResult : public CVC4::api::Result {
      friend class Solver;
     public:
      bool isSat() const {
        return d_result->getType() == CVC4::Result::TYPE_SAT
               && d_result->isSat() == CVC4::Result::SAT;
      }
      bool isUnsat() const {
        return d_result->getType() == CVC4::Result::TYPE_SAT
               && d_result->isSat() == CVC4::Result::UNSAT;
      }
      bool isSatUnknown() const {
        return d_result->getType() == CVC4::Result::TYPE_SAT
               && d_result->isSat() == CVC4::Result::SAT_UNKNOWN;
      }
      bool isValid() const {
        return d_result->getType() == CVC4::Result::TYPE_VALIDITY
               && d_result->isValid() == CVC4::Result::VALID;
      }
      bool isInvalid() const {
        return d_result->getType() == CVC4::Result::TYPE_VALIDITY
               && d_result->isValid() == CVC4::Result::INVALID;
      }
      bool isValidUnknown() const {
        return d_result->getType() == CVC4::Result::TYPE_VALIDITY
               && d_result->isValid() == CVC4::Result::VALIDITY_UNKNOWN;
      }
      bool equals (const Result& r) const {
        return *d_result == *r.d_result;
      }
      std::string getUnknownExplanation() const {
        std::stringstream ss;
        ss << d_result->whyUnknown();
        return ss.str();
      }
      std::string toString() const {
        return d_result->toString();
      }

     private:
      Result(const CVC4::Result& r) : d_result(new CVC4::Result(r)) {}
      std::shared_ptr<CVC4::Result> d_result;
    }; // class api::Result
  }  // namespace api
}  // namespace CVC4

%ignore CVC4::api::Result;
%include "api/cvc4cpp.h"
%{
namespace CVC4 {
  namespace api {
    typedef CVC4::api::Result ApiResult;
  }
}
%}
*/
