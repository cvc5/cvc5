namespace CVC4 {

template <class T>
class JavaIteratorAdapter {
  const T& d_t;
  typename T::const_iterator d_it;

public:
  JavaIteratorAdapter(const T& t) :
    d_t(t),
    d_it(d_t.begin()) {
  }

  bool hasNext() {
    return d_it != d_t.end();
  }

  typename T::const_iterator::value_type getNext() {
    typename T::const_iterator::value_type ret = *d_it;
    ++d_it;
    return ret;
  }
};/* class JavaIteratorAdapter<T> */

}/* CVC4 namespace */
