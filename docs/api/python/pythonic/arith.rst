Arithmetic
============


Basic Arithmetic Term Builders
-------------------------------
.. autofunction:: cvc5_z3py_compat.Int
.. autofunction:: cvc5_z3py_compat.Real
.. autofunction:: cvc5_z3py_compat.IntVal
.. autofunction:: cvc5_z3py_compat.RealVal
.. autofunction:: cvc5_z3py_compat.RatVal
.. autofunction:: cvc5_z3py_compat.Q
.. autofunction:: cvc5_z3py_compat.IntSort
.. autofunction:: cvc5_z3py_compat.RealSort
.. autofunction:: cvc5_z3py_compat.FreshInt
.. autofunction:: cvc5_z3py_compat.Ints
.. autofunction:: cvc5_z3py_compat.IntVector
.. autofunction:: cvc5_z3py_compat.FreshReal
.. autofunction:: cvc5_z3py_compat.Reals
.. autofunction:: cvc5_z3py_compat.RealVector


Arithmetic Overloads
--------------------

See the following operator overloads for building arithmetic terms. These terms
can also be built with builder functions listed below.

addition (``+``)
  :py:meth:`cvc5_z3py_compat.ArithRef.__add__`

subtraction (``-``)
  :py:meth:`cvc5_z3py_compat.ArithRef.__sub__`

multiplication (``*``)
  :py:meth:`cvc5_z3py_compat.ArithRef.__mul__`

division (``/``)
  :py:meth:`cvc5_z3py_compat.ArithRef.__div__`

power (``**``)
  :py:meth:`cvc5_z3py_compat.ArithRef.__pow__`

negation (``-``)
  :py:meth:`cvc5_z3py_compat.ArithRef.__neg__`

greater than (``>``)
  :py:meth:`cvc5_z3py_compat.ArithRef.__gt__`

less than (``<``)
  :py:meth:`cvc5_z3py_compat.ArithRef.__lt__`

greater than or equal to (``>=``)
  :py:meth:`cvc5_z3py_compat.ArithRef.__ge__`

less than or equal to (``<=``)
  :py:meth:`cvc5_z3py_compat.ArithRef.__le__`

equal (``==``)
  :py:meth:`cvc5_z3py_compat.ExprRef.__eq__`

not equal (``!=``)
  :py:meth:`cvc5_z3py_compat.ExprRef.__ne__`

.. autofunction:: cvc5_z3py_compat.Add
.. autofunction:: cvc5_z3py_compat.Mult
.. autofunction:: cvc5_z3py_compat.Sub
.. autofunction:: cvc5_z3py_compat.UMinus
.. autofunction:: cvc5_z3py_compat.Div
.. autofunction:: cvc5_z3py_compat.Pow
.. autofunction:: cvc5_z3py_compat.IntsModulus
.. autofunction:: cvc5_z3py_compat.Leq
.. autofunction:: cvc5_z3py_compat.Geq
.. autofunction:: cvc5_z3py_compat.Lt
.. autofunction:: cvc5_z3py_compat.Gt

Other Arithmetic Operators
--------------------------

.. autofunction:: cvc5_z3py_compat.ToReal
.. autofunction:: cvc5_z3py_compat.ToInt
.. autofunction:: cvc5_z3py_compat.IsInt
.. autofunction:: cvc5_z3py_compat.Sqrt
.. autofunction:: cvc5_z3py_compat.Cbrt

Testers
-------------------
.. autofunction:: cvc5_z3py_compat.is_arith
.. autofunction:: cvc5_z3py_compat.is_int
.. autofunction:: cvc5_z3py_compat.is_real
.. autofunction:: cvc5_z3py_compat.is_int_value
.. autofunction:: cvc5_z3py_compat.is_rational_value
.. autofunction:: cvc5_z3py_compat.is_arith_sort
.. autofunction:: cvc5_z3py_compat.is_add
.. autofunction:: cvc5_z3py_compat.is_mul
.. autofunction:: cvc5_z3py_compat.is_sub
.. autofunction:: cvc5_z3py_compat.is_div
.. autofunction:: cvc5_z3py_compat.is_idiv
.. autofunction:: cvc5_z3py_compat.is_mod
.. autofunction:: cvc5_z3py_compat.is_le
.. autofunction:: cvc5_z3py_compat.is_lt
.. autofunction:: cvc5_z3py_compat.is_ge
.. autofunction:: cvc5_z3py_compat.is_gt
.. autofunction:: cvc5_z3py_compat.is_is_int
.. autofunction:: cvc5_z3py_compat.is_to_real
.. autofunction:: cvc5_z3py_compat.is_to_int

Classes (with overloads)
-------------------------

.. autoclass:: cvc5_z3py_compat.ArithSortRef
   :members:
   :special-members:
.. autoclass:: cvc5_z3py_compat.ArithRef
   :members:
   :special-members:
.. autoclass:: cvc5_z3py_compat.IntNumRef
   :members:
   :special-members:
.. autoclass:: cvc5_z3py_compat.RatNumRef
   :members:
   :special-members:
