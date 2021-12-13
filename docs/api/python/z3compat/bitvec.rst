Bit-Vectors
============


Basic Bit-Vector Term Builders
----------------------------------
.. autofunction:: cvc5_z3py_compat.BitVec
.. autofunction:: cvc5_z3py_compat.BitVecVal
.. autofunction:: cvc5_z3py_compat.BitVecSort
.. autofunction:: cvc5_z3py_compat.BitVecs

Bit-Vector Operators
-----------------------------

.. autofunction:: cvc5_z3py_compat.BV2Int
.. autofunction:: cvc5_z3py_compat.Int2BV
.. autofunction:: cvc5_z3py_compat.Concat
.. autofunction:: cvc5_z3py_compat.Extract
.. autofunction:: cvc5_z3py_compat.ULE
.. autofunction:: cvc5_z3py_compat.ULT
.. autofunction:: cvc5_z3py_compat.UGE
.. autofunction:: cvc5_z3py_compat.UGT
.. autofunction:: cvc5_z3py_compat.UDiv
.. autofunction:: cvc5_z3py_compat.URem
.. autofunction:: cvc5_z3py_compat.SRem
.. autofunction:: cvc5_z3py_compat.LShR
.. autofunction:: cvc5_z3py_compat.RotateLeft
.. autofunction:: cvc5_z3py_compat.RotateRight
.. autofunction:: cvc5_z3py_compat.SignExt
.. autofunction:: cvc5_z3py_compat.ZeroExt
.. autofunction:: cvc5_z3py_compat.RepeatBitVec
.. autofunction:: cvc5_z3py_compat.BVRedAnd
.. autofunction:: cvc5_z3py_compat.BVRedOr

See the following operator overloads for buildign other kinds of bit-vector
terms:

* arithmetic

  * :py:meth:`cvc5_z3py_compat.BitVecRef.__add__`
  * :py:meth:`cvc5_z3py_compat.BitVecRef.__sub__`
  * :py:meth:`cvc5_z3py_compat.BitVecRef.__mul__`
  * :py:meth:`cvc5_z3py_compat.BitVecRef.__div__`

* bit-wise

  * :py:meth:`cvc5_z3py_compat.BitVecRef.__or__`
  * :py:meth:`cvc5_z3py_compat.BitVecRef.__and__`
  * :py:meth:`cvc5_z3py_compat.BitVecRef.__xor__`
  * :py:meth:`cvc5_z3py_compat.BitVecRef.__invert__`
  * :py:meth:`cvc5_z3py_compat.BitVecRef.__neg__`
  * :py:meth:`cvc5_z3py_compat.BitVecRef.__lshift__`
  * :py:meth:`cvc5_z3py_compat.BitVecRef.__rshift__`

* comparisons

  * :py:meth:`cvc5_z3py_compat.BitVecRef.__gt__`
  * :py:meth:`cvc5_z3py_compat.BitVecRef.__lt__`
  * :py:meth:`cvc5_z3py_compat.BitVecRef.__ge__`
  * :py:meth:`cvc5_z3py_compat.BitVecRef.__le__`
  * :py:meth:`cvc5_z3py_compat.ExprRef.__eq__`
  * :py:meth:`cvc5_z3py_compat.ExprRef.__ne__`

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
