Sets
============


Basic Set Term Builders
-------------------------

.. autofunction:: cvc5_z3py_compat.SetSort
.. autofunction:: cvc5_z3py_compat.Set
.. autofunction:: cvc5_z3py_compat.EmptySet
.. autofunction:: cvc5_z3py_compat.Singleton
.. autofunction:: cvc5_z3py_compat.FullSet

Set Operators
-------------------

.. autofunction:: cvc5_z3py_compat.SetUnion
.. autofunction:: cvc5_z3py_compat.SetIntersect
.. autofunction:: cvc5_z3py_compat.SetAdd
.. autofunction:: cvc5_z3py_compat.SetDel
.. autofunction:: cvc5_z3py_compat.SetComplement
.. autofunction:: cvc5_z3py_compat.SetDifference
.. autofunction:: cvc5_z3py_compat.SetMinus
.. autofunction:: cvc5_z3py_compat.IsMember
.. autofunction:: cvc5_z3py_compat.IsSubset

See the following operator overload for set terms:

* is member: :py:meth:`cvc5_z3py_compat.SetRef.__getitem__`


Classes (with overloads)
------------------------

.. autoclass:: cvc5_z3py_compat.SetSortRef
  :members:
  :special-members:
.. autoclass:: cvc5_z3py_compat.SetRef
  :members:
  :special-members:
