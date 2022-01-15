Arrays
============


Basic Array Term Builders
-------------------------

.. autofunction:: cvc5_z3py_compat.Array
.. autofunction:: cvc5_z3py_compat.ConstArray
.. autofunction:: cvc5_z3py_compat.K
.. autofunction:: cvc5_z3py_compat.ArraySort

Array Operators
-------------------

.. autofunction:: cvc5_z3py_compat.Select
.. autofunction:: cvc5_z3py_compat.Store
.. autofunction:: cvc5_z3py_compat.Update

See the following operator overloads for building other kinds of array
terms:

* ``select``: :py:meth:`cvc5_z3py_compat.ArrayRef.__getitem__`


Testers
-------------------
.. autofunction:: cvc5_z3py_compat.is_array_sort
.. autofunction:: cvc5_z3py_compat.is_array
.. autofunction:: cvc5_z3py_compat.is_const_array
.. autofunction:: cvc5_z3py_compat.is_K
.. autofunction:: cvc5_z3py_compat.is_select
.. autofunction:: cvc5_z3py_compat.is_store
.. autofunction:: cvc5_z3py_compat.is_update


Classes (with overloads)
------------------------

.. autoclass:: cvc5_z3py_compat.ArraySortRef
  :members:
  :special-members:
.. autoclass:: cvc5_z3py_compat.ArrayRef
  :members:
  :special-members:
