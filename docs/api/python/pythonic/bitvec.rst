Bit-Vectors
============


Basic Bit-Vector Term Builders
----------------------------------
.. autofunction:: cvc5_z3py_compat.BitVec
.. autofunction:: cvc5_z3py_compat.BitVecVal
.. autofunction:: cvc5_z3py_compat.BitVecSort
.. autofunction:: cvc5_z3py_compat.BitVecs

Bit-Vector Overloads
--------------------

See the following operator overloads for building bit-vector terms.
Each kind of term can also be built with a builder function below.

* arithmetic

  addition (``+``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__add__`

  subtraction (``-``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__sub__`

  multiplication (``*``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__mul__`

  division (``/``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__div__`

* bit-wise

  or (``|``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__or__`

  and (``&``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__and__`

  xor (``^``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__xor__`

  bit complement (``~``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__invert__`

  negation (``-``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__neg__`

  left shift (``<<``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__lshift__`

  right shift (``>>``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__rshift__`

* comparisons

  signed greater than (``>``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__gt__`

  signed less than (``<``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__lt__`

  signed greater than or equal to (``>=``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__ge__`

  signed less than or equal to (``<=``)
    :py:meth:`cvc5_z3py_compat.BitVecRef.__le__`

  equal (``==``)
    :py:meth:`cvc5_z3py_compat.ExprRef.__eq__`

  not equal (``!=``)
    :py:meth:`cvc5_z3py_compat.ExprRef.__ne__`

Bit-Vector Term Builders
------------------------

.. autofunction:: cvc5_z3py_compat.BV2Int
.. autofunction:: cvc5_z3py_compat.Int2BV
.. autofunction:: cvc5_z3py_compat.Concat
.. autofunction:: cvc5_z3py_compat.Extract
.. autofunction:: cvc5_z3py_compat.ULE
.. autofunction:: cvc5_z3py_compat.ULT
.. autofunction:: cvc5_z3py_compat.UGE
.. autofunction:: cvc5_z3py_compat.UGT
.. autofunction:: cvc5_z3py_compat.SLE
.. autofunction:: cvc5_z3py_compat.SLT
.. autofunction:: cvc5_z3py_compat.SGE
.. autofunction:: cvc5_z3py_compat.SGT
.. autofunction:: cvc5_z3py_compat.UDiv
.. autofunction:: cvc5_z3py_compat.URem
.. autofunction:: cvc5_z3py_compat.SDiv
.. autofunction:: cvc5_z3py_compat.SMod
.. autofunction:: cvc5_z3py_compat.SRem
.. autofunction:: cvc5_z3py_compat.LShR
.. autofunction:: cvc5_z3py_compat.RotateLeft
.. autofunction:: cvc5_z3py_compat.RotateRight
.. autofunction:: cvc5_z3py_compat.SignExt
.. autofunction:: cvc5_z3py_compat.ZeroExt
.. autofunction:: cvc5_z3py_compat.RepeatBitVec
.. autofunction:: cvc5_z3py_compat.BVRedAnd
.. autofunction:: cvc5_z3py_compat.BVRedOr
.. autofunction:: cvc5_z3py_compat.BVAdd
.. autofunction:: cvc5_z3py_compat.BVMult
.. autofunction:: cvc5_z3py_compat.BVSub
.. autofunction:: cvc5_z3py_compat.BVOr
.. autofunction:: cvc5_z3py_compat.BVAnd
.. autofunction:: cvc5_z3py_compat.BVXor
.. autofunction:: cvc5_z3py_compat.BVNeg
.. autofunction:: cvc5_z3py_compat.BVNot


Testers
-------------------
.. autofunction:: cvc5_z3py_compat.is_bv_sort
.. autofunction:: cvc5_z3py_compat.is_bv
.. autofunction:: cvc5_z3py_compat.is_bv_value

Classes (with overloads)
-----------------------------

.. autoclass:: cvc5_z3py_compat.BitVecSortRef
   :members:
   :special-members:
.. autoclass:: cvc5_z3py_compat.BitVecRef
   :members:
   :special-members:
.. autoclass:: cvc5_z3py_compat.BitVecNumRef
   :members:
   :special-members:
