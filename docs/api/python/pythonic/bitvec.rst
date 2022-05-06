Bit-Vectors
============


Basic Bit-Vector Term Builders
----------------------------------
.. autofunction:: cvc5.pythonic.BitVec
.. autofunction:: cvc5.pythonic.BitVecVal
.. autofunction:: cvc5.pythonic.BitVecSort
.. autofunction:: cvc5.pythonic.BitVecs

Bit-Vector Overloads
--------------------

See the following operator overloads for building bit-vector terms.
Each kind of term can also be built with a builder function below.

* arithmetic

  addition (``+``)
    :py:meth:`cvc5.pythonic.BitVecRef.__add__`

  subtraction (``-``)
    :py:meth:`cvc5.pythonic.BitVecRef.__sub__`

  multiplication (``*``)
    :py:meth:`cvc5.pythonic.BitVecRef.__mul__`

  division (``/``)
    :py:meth:`cvc5.pythonic.BitVecRef.__div__`

* bit-wise

  or (``|``)
    :py:meth:`cvc5.pythonic.BitVecRef.__or__`

  and (``&``)
    :py:meth:`cvc5.pythonic.BitVecRef.__and__`

  xor (``^``)
    :py:meth:`cvc5.pythonic.BitVecRef.__xor__`

  bit complement (``~``)
    :py:meth:`cvc5.pythonic.BitVecRef.__invert__`

  negation (``-``)
    :py:meth:`cvc5.pythonic.BitVecRef.__neg__`

  left shift (``<<``)
    :py:meth:`cvc5.pythonic.BitVecRef.__lshift__`

  right shift (``>>``)
    :py:meth:`cvc5.pythonic.BitVecRef.__rshift__`

* comparisons

  signed greater than (``>``)
    :py:meth:`cvc5.pythonic.BitVecRef.__gt__`

  signed less than (``<``)
    :py:meth:`cvc5.pythonic.BitVecRef.__lt__`

  signed greater than or equal to (``>=``)
    :py:meth:`cvc5.pythonic.BitVecRef.__ge__`

  signed less than or equal to (``<=``)
    :py:meth:`cvc5.pythonic.BitVecRef.__le__`

  equal (``==``)
    :py:meth:`cvc5.pythonic.ExprRef.__eq__`

  not equal (``!=``)
    :py:meth:`cvc5.pythonic.ExprRef.__ne__`

Bit-Vector Term Builders
------------------------

.. autofunction:: cvc5.pythonic.BV2Int
.. autofunction:: cvc5.pythonic.Int2BV
.. autofunction:: cvc5.pythonic.Concat
.. autofunction:: cvc5.pythonic.Extract
.. autofunction:: cvc5.pythonic.ULE
.. autofunction:: cvc5.pythonic.ULT
.. autofunction:: cvc5.pythonic.UGE
.. autofunction:: cvc5.pythonic.UGT
.. autofunction:: cvc5.pythonic.SLE
.. autofunction:: cvc5.pythonic.SLT
.. autofunction:: cvc5.pythonic.SGE
.. autofunction:: cvc5.pythonic.SGT
.. autofunction:: cvc5.pythonic.UDiv
.. autofunction:: cvc5.pythonic.URem
.. autofunction:: cvc5.pythonic.SDiv
.. autofunction:: cvc5.pythonic.SMod
.. autofunction:: cvc5.pythonic.SRem
.. autofunction:: cvc5.pythonic.LShR
.. autofunction:: cvc5.pythonic.RotateLeft
.. autofunction:: cvc5.pythonic.RotateRight
.. autofunction:: cvc5.pythonic.SignExt
.. autofunction:: cvc5.pythonic.ZeroExt
.. autofunction:: cvc5.pythonic.RepeatBitVec
.. autofunction:: cvc5.pythonic.BVRedAnd
.. autofunction:: cvc5.pythonic.BVRedOr
.. autofunction:: cvc5.pythonic.BVAdd
.. autofunction:: cvc5.pythonic.BVMult
.. autofunction:: cvc5.pythonic.BVSub
.. autofunction:: cvc5.pythonic.BVOr
.. autofunction:: cvc5.pythonic.BVAnd
.. autofunction:: cvc5.pythonic.BVXor
.. autofunction:: cvc5.pythonic.BVNeg
.. autofunction:: cvc5.pythonic.BVNot


Testers
-------------------
.. autofunction:: cvc5.pythonic.is_bv_sort
.. autofunction:: cvc5.pythonic.is_bv
.. autofunction:: cvc5.pythonic.is_bv_value

Classes (with overloads)
-----------------------------

.. autoclass:: cvc5.pythonic.BitVecSortRef
   :members:
   :special-members:
.. autoclass:: cvc5.pythonic.BitVecRef
   :members:
   :special-members:
.. autoclass:: cvc5.pythonic.BitVecNumRef
   :members:
   :special-members:
