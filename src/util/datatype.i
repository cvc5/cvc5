%{
#include "util/datatype.h"
%}

namespace CVC4 {
%rename(DatatypeConstructor) CVC4::Datatype::Constructor;
%rename(DatatypeConstructor) CVC4::Constructor;
}

%extend std::vector< CVC4::Datatype > {
  %ignore vector(size_type);
};
%template(vectorDatatype) std::vector< CVC4::Datatype >;

%extend std::vector< CVC4::Datatype::Constructor > {
  %ignore vector(size_type);
};
%template(vectorDatatypeConstructor) std::vector< CVC4::Datatype::Constructor >;

%rename(equals) CVC4::Datatype::operator==(const Datatype&) const;
%ignore CVC4::Datatype::operator!=(const Datatype&) const;

%rename(beginConst) CVC4::Datatype::begin() const;
%rename(endConst) CVC4::Datatype::end() const;

%rename(getConstructor) CVC4::Datatype::operator[](size_t) const;

%rename(apply) CVC4::DatatypeHashFunction::operator()(const Datatype&) const;
%ignore CVC4::DatatypeHashFunction::operator()(const Datatype*) const;
%rename(apply) CVC4::DatatypeHashFunction::operator()(const Datatype::Constructor&) const;
%ignore CVC4::DatatypeHashFunction::operator()(const Datatype::Constructor*) const;

%rename(beginConst) CVC4::Constructor::begin() const;
%rename(endConst) CVC4::Constructor::end() const;

%rename(getArg) CVC4::Constructor::operator[](size_t) const;

%ignore CVC4::operator<<(std::ostream&, const Datatype&);
%ignore CVC4::operator<<(std::ostream&, const Datatype::Constructor&);
%ignore CVC4::operator<<(std::ostream&, const Datatype::Constructor::Arg&);

%feature("valuewrapper") CVC4::Datatype::UnresolvedType;
%feature("valuewrapper") CVC4::Datatype::Constructor;

%include "util/datatype.h"

namespace CVC4 {
    class CVC4_PUBLIC Arg {

      std::string d_name;
      Expr d_selector;
      /** the constructor associated with this selector */
      Expr d_constructor;
      bool d_resolved;

      explicit Arg(std::string name, Expr selector);
      friend class Constructor;
      friend class Datatype;

      bool isUnresolvedSelf() const throw();

    public:

      /** Get the name of this constructor argument. */
      std::string getName() const throw();

      /**
       * Get the selector for this constructor argument; this call is
       * only permitted after resolution.
       */
      Expr getSelector() const;

      /**
       * Get the associated constructor for this constructor argument;
       * this call is only permitted after resolution.
       */
      Expr getConstructor() const;

      /**
       * Get the selector for this constructor argument; this call is
       * only permitted after resolution.
       */
      Type getSelectorType() const;

      /**
       * Get the name of the type of this constructor argument
       * (Datatype field).  Can be used for not-yet-resolved Datatypes
       * (in which case the name of the unresolved type, or "[self]"
       * for a self-referential type is returned).
       */
      std::string getSelectorTypeName() const;

      /**
       * Returns true iff this constructor argument has been resolved.
       */
      bool isResolved() const throw();

    };/* class Datatype::Constructor::Arg */

  class Constructor {
  public:

    /** The type for iterators over constructor arguments. */
    typedef std::vector<Arg>::iterator iterator;
    /** The (const) type for iterators over constructor arguments. */
    typedef std::vector<Arg>::const_iterator const_iterator;

  private:

    std::string d_name;
    Expr d_constructor;
    Expr d_tester;
    std::vector<Arg> d_args;

    void resolve(ExprManager* em, DatatypeType self,
                 const std::map<std::string, DatatypeType>& resolutions,
                 const std::vector<Type>& placeholders,
                 const std::vector<Type>& replacements,
                 const std::vector< SortConstructorType >& paramTypes,
                 const std::vector< DatatypeType >& paramReplacements)
      throw(AssertionException, DatatypeResolutionException);
    friend class Datatype;

    /** @FIXME document this! */
    Type doParametricSubstitution(Type range,
                                  const std::vector< SortConstructorType >& paramTypes,
                                  const std::vector< DatatypeType >& paramReplacements);
  public:
    /**
     * Create a new Datatype constructor with the given name for the
     * constructor and the given name for the tester.  The actual
     * constructor and tester aren't created until resolution time.
     */
    explicit Constructor(std::string name, std::string tester);

    /**
     * Add an argument (i.e., a data field) of the given name and type
     * to this Datatype constructor.
     */
    void addArg(std::string selectorName, Type selectorType);

    /**
     * Add an argument (i.e., a data field) of the given name to this
     * Datatype constructor that refers to an as-yet-unresolved
     * Datatype (which may be mutually-recursive).
     */
    void addArg(std::string selectorName, Datatype::UnresolvedType selectorType);

    /**
     * Add a self-referential (i.e., a data field) of the given name
     * to this Datatype constructor that refers to the enclosing
     * Datatype.  For example, using the familiar "nat" Datatype, to
     * create the "pred" field for "succ" constructor, one uses
     * succ::addArg("pred", Datatype::SelfType())---the actual Type
     * cannot be passed because the Datatype is still under
     * construction.
     *
     * This is a special case of
     * Constructor::addArg(std::string, Datatype::UnresolvedType).
     */
    void addArg(std::string selectorName, Datatype::SelfType);

    /** Get the name of this Datatype constructor. */
    std::string getName() const throw();
    /**
     * Get the constructor operator of this Datatype constructor.  The
     * Datatype must be resolved.
     */
    Expr getConstructor() const;
    /**
     * Get the tester operator of this Datatype constructor.  The
     * Datatype must be resolved.
     */
    Expr getTester() const;
    /**
     * Get the number of arguments (so far) of this Datatype constructor.
     */
    inline size_t getNumArgs() const throw();

    /**
     * Get the specialized constructor type for a parametric
     * constructor; this call is only permitted after resolution.
     */
    Type getSpecializedConstructorType(Type returnType) const;

    /**
     * Return the cardinality of this constructor (the product of the
     * cardinalities of its arguments).
     */
    Cardinality getCardinality() const throw(AssertionException);

    /**
     * Return true iff this constructor is finite (it is nullary or
     * each of its argument types are finite).  This function can
     * only be called for resolved constructors.
     */
    bool isFinite() const throw(AssertionException);

    /**
     * Return true iff this constructor is well-founded (there exist
     * ground terms).  The constructor must be resolved or an
     * exception is thrown.
     */
    bool isWellFounded() const throw(AssertionException);

    /**
     * Construct and return a ground term of this constructor.  The
     * constructor must be both resolved and well-founded, or else an
     * exception is thrown.
     */
    Expr mkGroundTerm( Type t ) const throw(AssertionException);

    /**
     * Returns true iff this Datatype constructor has already been
     * resolved.
     */
    inline bool isResolved() const throw();

    /** Get the beginning iterator over Constructor args. */
    inline iterator begin() throw();
    /** Get the ending iterator over Constructor args. */
    inline iterator end() throw();
    /** Get the beginning const_iterator over Constructor args. */
    inline const_iterator begin() const throw();
    /** Get the ending const_iterator over Constructor args. */
    inline const_iterator end() const throw();

    /** Get the ith Constructor arg. */
    const Arg& operator[](size_t index) const;

  };/* class Datatype::Constructor */

  class SelfType {
  };/* class Datatype::SelfType */

  /**
   * An unresolved type (used in calls to
   * Datatype::Constructor::addArg()) to allow a Datatype to refer to
   * itself or to other mutually-recursive Datatypes.  Unresolved-type
   * fields of Datatypes will be properly typed when a Type is created
   * for the Datatype by the ExprManager (which calls
   * Datatype::resolve()).
   */
  class UnresolvedType {
    std::string d_name;
  public:
    inline UnresolvedType(std::string name);
    inline std::string getName() const throw();
  };/* class Datatype::UnresolvedType */
}

%{
namespace CVC4 {
typedef Datatype::Constructor Constructor;
typedef Datatype::Constructor::Arg Arg;
typedef Datatype::SelfType SelfType;
typedef Datatype::UnresolvedType UnresolvedType;
}
%}

