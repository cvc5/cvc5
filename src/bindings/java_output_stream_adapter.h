namespace CVC4 {

class JavaOutputStreamAdapter {
  std::stringstream d_ss;

public:
  JavaOutputStreamAdapter() { }

  std::string toString() { return d_ss.str(); }

};/* class JavaOutputStreamAdapter */

}/* CVC4 namespace */
