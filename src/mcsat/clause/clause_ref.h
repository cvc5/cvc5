#pragma once

#include "cvc4_private.h"

#include <cstddef>
#include <iostream>
#include <boost/integer/integer_mask.hpp>

#include "mcsat/clause/clause.h"

namespace CVC4 {
namespace mcsat {

class ClauseDatabase;

/** A reference to a clause */
class CRef {

  /** Number of bits kept for the reference */
  static const size_t BITS_FOR_REFERENCE = 60;
  
  /** NUmber of bits kept for the database id */
  static const size_t BITS_FOR_DATABASE  = 4;

  /** Null reference */
  static const size_t nullRef = boost::low_bits_mask_t<BITS_FOR_REFERENCE>::sig_bits;

private:
 
  /** Reference into the clause database */
  size_t d_ref : BITS_FOR_REFERENCE;
  
  /** Id of the clause database */
  size_t d_db  : BITS_FOR_DATABASE;
  
  /** 
   * Construct the reference. This one is not reference counted, as only the
   * clause database creates these.
   */
  CRef(size_t ref, size_t db)
  : d_ref(ref) 
  , d_db(db)
  {}

  /** Only clause database can create the references */
  friend class ClauseDatabase;

  /** Does this ref correspond to an actual clause */
  bool hasClause() const {
    if (d_ref == nullRef) return false;
    return true;
  }

public:

  /**
   * Copy constructor of the same type.
   */
  CRef(const CRef& other)
  : d_ref(other.d_ref)
  , d_db(other.d_db)
  {}

  /** Assignment operator */
  CRef& operator = (const CRef& other) {
    if (this != &other) {
      d_ref = other.d_ref;
      d_db = other.d_db;
    }
    return *this;
  }
  
  /** Default constructs null */
  CRef()
  : d_ref(nullRef)
  , d_db(0)
  {}

  /** The null clause reference */
  static const CRef null;

  /** Return the id of the database holding this clause */
  size_t getDatabaseId() const {
    return d_db;
  }
  
  /** Get the actual clause */
  Clause& getClause() const;

  /** Check if the reference is null */
  bool isNull() const {
    return *this == null;
  }
  
  /** Print the clause to the stream */
  void toStream(std::ostream& out) const;

  /** Hash the reference */
  size_t hash() const {
    return std::tr1::hash<size_t>()(d_ref);
  }

  /** Compare two references */
  bool operator == (const CRef& other) const {
    return d_db == other.d_db && d_ref == other.d_ref;
  }

  /** Compare two references (by pointer value) */
  bool operator < (const CRef& other) const {
    if (d_db == other.d_db) {
      return d_ref < other.d_ref;
    } else {
      return d_db < other.d_db;
    }
  }
};

inline std::ostream& operator << (std::ostream& out, const CRef& cRef) {
  cRef.toStream(out);
  return out;
}

struct CRefHashFunction {
  size_t operator () (const CRef& cRef) const {
    return cRef.hash();
  }
};


} /* namespace mcsat */
} /* namespace CVC4 */


