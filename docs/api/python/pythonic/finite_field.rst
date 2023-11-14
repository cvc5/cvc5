Finite Fields
=============


Basic FiniteField Term Builders
-------------------------------
.. autofunction:: cvc5.pythonic.FiniteFieldElem
.. autofunction:: cvc5.pythonic.FiniteFieldVal
.. autofunction:: cvc5.pythonic.FiniteFieldSort
.. autofunction:: cvc5.pythonic.FiniteFieldElems


Arithmetic Overloads
--------------------

See the following operator overloads for building finite field terms. These
terms can also be built with builder functions listed below.

addition (``+``)
  :py:meth:`cvc5.pythonic.FiniteFieldRef.__add__`

subtraction (``-``)
  :py:meth:`cvc5.pythonic.FiniteFieldRef.__sub__`

negation (``-``)
  :py:meth:`cvc5.pythonic.FiniteFieldRef.__neg__`

multiplication (``*``)
  :py:meth:`cvc5.pythonic.FiniteFieldRef.__mul__`

equality (``==``)
  :py:meth:`cvc5.pythonic.ExprRef.__eq__`

.. autofunction:: cvc5.pythonic.FFAdd
.. autofunction:: cvc5.pythonic.FFSub
.. autofunction:: cvc5.pythonic.FFNeg
.. autofunction:: cvc5.pythonic.FFMult


Testers
-------------------
.. autofunction:: cvc5.pythonic.is_ff_sort
.. autofunction:: cvc5.pythonic.is_ff
.. autofunction:: cvc5.pythonic.is_ff_value

Classes (with overloads)
-------------------------

.. autoclass:: cvc5.pythonic.FiniteFieldSortRef
   :members:
   :special-members:
.. autoclass:: cvc5.pythonic.FiniteFieldRef
   :members:
   :special-members:
.. autoclass:: cvc5.pythonic.FiniteFieldNumRef
   :members:
   :special-members:

