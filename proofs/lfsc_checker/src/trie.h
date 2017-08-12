#ifndef sc2__trie_h
#define sc2__trie_h

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <vector>

template<class Data>
class Trie {
protected:
  char *str;
  Data d;
  bool using_next;
  std::vector<Trie<Data> *> next;

  // s is assumed to be non-empty (and non-null)
  Data insert_next(const char *s, const Data &x) {
    assert(s != NULL && s[0] != '\0');
    unsigned c = s[0];
    if (c >= next.size()) {
      using_next = true;
      next.resize(c+1);
      next[c] = new Trie<Data>;
    }
    else if (!next[c]) 
      next[c] = new Trie<Data>;

    return next[c]->insert(&s[1], x);
  }

  // s is assumed to be non-empty (and non-null)
  Data get_next(const char *s) {
    assert(s != NULL && s[0] != '\0');
    unsigned c = s[0];
    if (c >= next.size())
      return Data();
    Trie<Data> *n = next[c];
    if (!n)
      return Data();
    return n->get(&s[1]);
  }

public:
  Trie() : str(), d(), using_next(false), next() { }

  ~Trie();

  class Cleaner {
  public:
    virtual ~Cleaner() {}
    virtual void clean(Data d) = 0;
  };

  static Cleaner *cleaner;

  Data get(const char *s) {
    if (!s[0] && (!str || !str[0]))
      return d;
    if (str && strcmp(str, s) == 0) return d;
    if (using_next)
      return get_next(s);
    return Data();
  }

  Data insert(const char *s, const Data &x) {
    if (s[0] == 0) {
      // we need to insert x right here.
      if (str) {
	if (str[0] == 0) {
	  // we need to replace d with x
	  Data old = d;
	  d = x;
	  return old;
	}
	// we need to push str into next.
	(void)insert_next(str,d);
	free(str);
      }
      str = strdup(s);
      d = x;
      return Data();
    }
    
    if (str) {
      // cannot store x here 
      if (str[0] != 0) {
	insert_next(str,d);
	free(str);
	str = 0;
	d = Data();
      }
      return insert_next(s,x);
    }

    if (using_next)
      // also cannot store x here 
      return insert_next(s,x);

    // we can insert x here as an optimization
    str = strdup(s);
    d = x;
    return Data();
  }

};

template<class Data> 
Trie<Data>::~Trie() 
{
  cleaner->clean(d);
  for (int i = 0, iend = next.size(); i < iend; i++) {
    Trie *t = next[i];
    if (t)
      delete t;
  }
  if (str)
    free(str);
}

extern void unit_test_trie();

#endif
