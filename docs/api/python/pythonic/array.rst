Arrays
============


Basic Array Term Builders
-------------------------

.. autofunction:: cvc5.pythonic.Array
.. autofunction:: cvc5.pythonic.ConstArray
.. autofunction:: cvc5.pythonic.K
.. autofunction:: cvc5.pythonic.ArraySort

Array Operators
-------------------

.. autofunction:: cvc5.pythonic.Select
.. autofunction:: cvc5.pythonic.Store
.. autofunction:: cvc5.pythonic.Update

See the following operator overloads for building other kinds of array
terms:

* ``select``: :py:meth:`cvc5.pythonic.ArrayRef.__getitem__`


Testers
-------------------
.. autofunction:: cvc5.pythonic.is_array_sort
.. autofunction:: cvc5.pythonic.is_array
.. autofunction:: cvc5.pythonic.is_const_array
.. autofunction:: cvc5.pythonic.is_K
.. autofunction:: cvc5.pythonic.is_select
.. autofunction:: cvc5.pythonic.is_store
.. autofunction:: cvc5.pythonic.is_update


Classes (with overloads)
------------------------

.. autoclass:: cvc5.pythonic.ArraySortRef
  :members:
  :special-members:
.. autoclass:: cvc5.pythonic.ArrayRef
  :members:
  :special-members:
