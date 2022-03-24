Sets
============


Basic Set Term Builders
-------------------------

.. autofunction:: cvc5.pythonic.SetSort
.. autofunction:: cvc5.pythonic.Set
.. autofunction:: cvc5.pythonic.EmptySet
.. autofunction:: cvc5.pythonic.Singleton
.. autofunction:: cvc5.pythonic.FullSet

Set Operators
-------------------

.. autofunction:: cvc5.pythonic.SetUnion
.. autofunction:: cvc5.pythonic.SetIntersect
.. autofunction:: cvc5.pythonic.SetAdd
.. autofunction:: cvc5.pythonic.SetDel
.. autofunction:: cvc5.pythonic.SetComplement
.. autofunction:: cvc5.pythonic.SetDifference
.. autofunction:: cvc5.pythonic.SetMinus
.. autofunction:: cvc5.pythonic.IsMember
.. autofunction:: cvc5.pythonic.IsSubset

See the following operator overload for set terms:

* is member: :py:meth:`cvc5.pythonic.SetRef.__getitem__`


Classes (with overloads)
------------------------

.. autoclass:: cvc5.pythonic.SetSortRef
  :members:
  :special-members:
.. autoclass:: cvc5.pythonic.SetRef
  :members:
  :special-members:
