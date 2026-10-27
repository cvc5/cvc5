API Documentation
=================

Alternatively to using cvc5 :doc:`as a binary <../binary/binary>`, cvc5 can be
integrated at the back end of other tools via one of its rich and comprehensive
APIs.

The primary interface of cvc5 is its :doc:`C++ API <cpp/cpp>`.
Its :doc:`C API <c/c>`, :doc:`Java API <java/java>` and
:doc:`base Python API <python/base/python>` implement a thin wrapper around
the C++ API.
In addition to the base Python API, cvc5 also provides a more :doc:`pythonic
Python API <python/pythonic/pythonic>` at
https://github.com/cvc5/cvc5_pythonic_api,
documented :doc:`here <python/pythonic/pythonic>`.

.. toctree::
   :maxdepth: 1

   cpp/cpp
   c/c
   java/java
   python/python
