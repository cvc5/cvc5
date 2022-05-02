Arithmetic
============


Basic Arithmetic Term Builders
-------------------------------
.. autofunction:: cvc5.pythonic.Int
.. autofunction:: cvc5.pythonic.Real
.. autofunction:: cvc5.pythonic.IntVal
.. autofunction:: cvc5.pythonic.RealVal
.. autofunction:: cvc5.pythonic.RatVal
.. autofunction:: cvc5.pythonic.Q
.. autofunction:: cvc5.pythonic.IntSort
.. autofunction:: cvc5.pythonic.RealSort
.. autofunction:: cvc5.pythonic.FreshInt
.. autofunction:: cvc5.pythonic.Ints
.. autofunction:: cvc5.pythonic.IntVector
.. autofunction:: cvc5.pythonic.FreshReal
.. autofunction:: cvc5.pythonic.Reals
.. autofunction:: cvc5.pythonic.RealVector


Arithmetic Overloads
--------------------

See the following operator overloads for building arithmetic terms. These terms
can also be built with builder functions listed below.

addition (``+``)
  :py:meth:`cvc5.pythonic.ArithRef.__add__`

subtraction (``-``)
  :py:meth:`cvc5.pythonic.ArithRef.__sub__`

multiplication (``*``)
  :py:meth:`cvc5.pythonic.ArithRef.__mul__`

division (``/``)
  :py:meth:`cvc5.pythonic.ArithRef.__div__`

power (``**``)
  :py:meth:`cvc5.pythonic.ArithRef.__pow__`

negation (``-``)
  :py:meth:`cvc5.pythonic.ArithRef.__neg__`

greater than (``>``)
  :py:meth:`cvc5.pythonic.ArithRef.__gt__`

less than (``<``)
  :py:meth:`cvc5.pythonic.ArithRef.__lt__`

greater than or equal to (``>=``)
  :py:meth:`cvc5.pythonic.ArithRef.__ge__`

less than or equal to (``<=``)
  :py:meth:`cvc5.pythonic.ArithRef.__le__`

equal (``==``)
  :py:meth:`cvc5.pythonic.ExprRef.__eq__`

not equal (``!=``)
  :py:meth:`cvc5.pythonic.ExprRef.__ne__`

.. autofunction:: cvc5.pythonic.Add
.. autofunction:: cvc5.pythonic.Mult
.. autofunction:: cvc5.pythonic.Sub
.. autofunction:: cvc5.pythonic.UMinus
.. autofunction:: cvc5.pythonic.Div
.. autofunction:: cvc5.pythonic.Pow
.. autofunction:: cvc5.pythonic.IntsModulus
.. autofunction:: cvc5.pythonic.Leq
.. autofunction:: cvc5.pythonic.Geq
.. autofunction:: cvc5.pythonic.Lt
.. autofunction:: cvc5.pythonic.Gt

Other Arithmetic Operators
--------------------------

.. autofunction:: cvc5.pythonic.ToReal
.. autofunction:: cvc5.pythonic.ToInt
.. autofunction:: cvc5.pythonic.IsInt
.. autofunction:: cvc5.pythonic.Sqrt
.. autofunction:: cvc5.pythonic.Cbrt

Transcendentals
--------------------------
.. autofunction:: cvc5.pythonic.Pi
.. autofunction:: cvc5.pythonic.Exponential
.. autofunction:: cvc5.pythonic.Sine
.. autofunction:: cvc5.pythonic.Cosine
.. autofunction:: cvc5.pythonic.Tangent
.. autofunction:: cvc5.pythonic.Arcsine
.. autofunction:: cvc5.pythonic.Arccosine
.. autofunction:: cvc5.pythonic.Arctangent
.. autofunction:: cvc5.pythonic.Secant
.. autofunction:: cvc5.pythonic.Cosecant
.. autofunction:: cvc5.pythonic.Cotangent
.. autofunction:: cvc5.pythonic.Arcsecant
.. autofunction:: cvc5.pythonic.Arccosecant
.. autofunction:: cvc5.pythonic.Arccotangent


Testers
-------------------
.. autofunction:: cvc5.pythonic.is_arith
.. autofunction:: cvc5.pythonic.is_int
.. autofunction:: cvc5.pythonic.is_real
.. autofunction:: cvc5.pythonic.is_int_value
.. autofunction:: cvc5.pythonic.is_rational_value
.. autofunction:: cvc5.pythonic.is_arith_sort
.. autofunction:: cvc5.pythonic.is_add
.. autofunction:: cvc5.pythonic.is_mul
.. autofunction:: cvc5.pythonic.is_sub
.. autofunction:: cvc5.pythonic.is_div
.. autofunction:: cvc5.pythonic.is_idiv
.. autofunction:: cvc5.pythonic.is_mod
.. autofunction:: cvc5.pythonic.is_le
.. autofunction:: cvc5.pythonic.is_lt
.. autofunction:: cvc5.pythonic.is_ge
.. autofunction:: cvc5.pythonic.is_gt
.. autofunction:: cvc5.pythonic.is_is_int
.. autofunction:: cvc5.pythonic.is_to_real
.. autofunction:: cvc5.pythonic.is_to_int

Classes (with overloads)
-------------------------

.. autoclass:: cvc5.pythonic.ArithSortRef
   :members:
   :special-members:
.. autoclass:: cvc5.pythonic.ArithRef
   :members:
   :special-members:
.. autoclass:: cvc5.pythonic.IntNumRef
   :members:
   :special-members:
.. autoclass:: cvc5.pythonic.RatNumRef
   :members:
   :special-members:
