#include "trie.h"
#include <iostream>

class Simple : public Trie<int>::Cleaner {
public:
  ~Simple() {}
  void clean(int p) {
    (void)p;
  }
};

template <>
Trie<int>::Cleaner *Trie<int>::cleaner = new Simple;

void unit_test_trie() {
  Trie<int> t;
  t.insert("a", 1);
  t.insert("b", 2);
  t.insert("abc", 3);
  t.insert("b", 0);
  std::cout << "a: " << t.get("a") << "\n";
  std::cout << "b: " << t.get("b") << "\n";
  std::cout << "abc: " << t.get("abc") << "\n";
}
