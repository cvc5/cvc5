/**
 * The following file is based on
 * https://github.com/swig/swig/blob/master/Lib/java/std_vector.i
 *
 * Note: The SWIG library is under a different license than SWIG itself. See
 * https://github.com/swig/swig/blob/master/LICENSE for details.
 *
 * This file define the macro SWIG_STD_VECTOR_EM to wrap a C++ std::vector for
 * Java, similar to the SWIG library. The core difference is that the utilities
 * in this file add a reference to an ExprManager to keep it alive as long as
 * the vector lives.
 */

%include <std_common.i>
%include <std_vector.i>

%{
#include <vector>
#include <stdexcept>
%}

%define SWIG_STD_VECTOR_EM(CTYPE, CONST_REFERENCE)
%typemap(javabase) std::vector< CTYPE > "java.util.AbstractList<$typemap(jstype, CTYPE)>"
%typemap(javainterfaces) std::vector< CTYPE > "java.util.RandomAccess"

%typemap(javabody) std::vector< CTYPE > %{
  private long swigCPtr;
  protected boolean swigCMemOwn;
  private ExprManager em;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
    this.em = em;
  }

  public $javaclassname(ExprManager em) {
    this();
    this.em = em;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javaconstruct) std::vector< CTYPE > {
  this(null, $imcall, true);
}

%javamethodmodifiers vector() "private";

%proxycode %{
  public $javaclassname(ExprManager em, $typemap(jstype, CTYPE)[] initialElements) {
    this(em);
    reserve(initialElements.length);

    for ($typemap(jstype, CTYPE) element : initialElements) {
      add(element);
    }
  }

  public $javaclassname(ExprManager em, Iterable<$typemap(jstype, CTYPE)> initialElements) {
    this(em);
    for ($typemap(jstype, CTYPE) element : initialElements) {
      add(element);
    }
  }

  public $typemap(jstype, CTYPE) get(int index) {
    return doGet(index);
  }

  public $typemap(jstype, CTYPE) set(int index, $typemap(jstype, CTYPE) e) {
    return doSet(index, e);
  }

  public boolean add($typemap(jstype, CTYPE) e) {
    modCount++;
    doAdd(e);
    return true;
  }

  public void add(int index, $typemap(jboxtype, CTYPE) e) {
    modCount++;
    doAdd(index, e);
  }

  public $typemap(jboxtype, CTYPE) remove(int index) {
    modCount++;
    return doRemove(index);
  }

  protected void removeRange(int fromIndex, int toIndex) {
    modCount++;
    doRemoveRange(fromIndex, toIndex);
  }

  public int size() {
    return doSize();
  }
%}

  public:
    typedef size_t size_type;
    typedef ptrdiff_t difference_type;
    typedef CTYPE value_type;
    typedef CTYPE *pointer;
    typedef CTYPE const *const_pointer;
    typedef CTYPE &reference;
    typedef CONST_REFERENCE const_reference;

    vector();
    size_type capacity() const;
    void reserve(size_type n) throw (std::length_error);
    %rename(isEmpty) empty;
    bool empty() const;
    void clear();
    %extend {
      %fragment("SWIG_VectorSize");

      vector(jint count, const CTYPE &value) throw (std::out_of_range) {
        if (count < 0)
          throw std::out_of_range("vector count must be positive");
        return new std::vector< CTYPE >(static_cast<std::vector< CTYPE >::size_type>(count), value);
      }

      jint doSize() const throw (std::out_of_range) {
        return SWIG_VectorSize(self->size());
      }

      void doAdd(const value_type& x) {
        self->push_back(x);
      }

      void doAdd(jint index, const value_type& x) throw (std::out_of_range) {
        jint size = static_cast<jint>(self->size());
        if (0 <= index && index <= size) {
          self->insert(self->begin() + index, x);
        } else {
          throw std::out_of_range("vector index out of range");
        }
      }

      value_type doRemove(jint index) throw (std::out_of_range) {
        jint size = static_cast<jint>(self->size());
        if (0 <= index && index < size) {
          CTYPE const old_value = (*self)[index];
          self->erase(self->begin() + index);
          return old_value;
        } else {
          throw std::out_of_range("vector index out of range");
        }
      }

      CONST_REFERENCE doGet(jint index) throw (std::out_of_range) {
        jint size = static_cast<jint>(self->size());
        if (index >= 0 && index < size)
          return (*self)[index];
        else
          throw std::out_of_range("vector index out of range");
      }

      value_type doSet(jint index, const value_type& val) throw (std::out_of_range) {
        jint size = static_cast<jint>(self->size());
        if (index >= 0 && index < size) {
          CTYPE const old_value = (*self)[index];
          (*self)[index] = val;
          return old_value;
        }
        else
          throw std::out_of_range("vector index out of range");
      }

      void doRemoveRange(jint fromIndex, jint toIndex) throw (std::out_of_range) {
        jint size = static_cast<jint>(self->size());
        if (0 <= fromIndex && fromIndex <= toIndex && toIndex <= size) {
          self->erase(self->begin() + fromIndex, self->begin() + toIndex);
        } else {
          throw std::out_of_range("vector index out of range");
        }
      }
    }

%enddef
