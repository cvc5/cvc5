Floating Point
==============

Basic FP Term Builders
-------------------------

.. autofunction:: cvc5_z3py_compat.FP
.. autofunction:: cvc5_z3py_compat.FPs
.. autofunction:: cvc5_z3py_compat.FPVal
.. autofunction:: cvc5_z3py_compat.fpNaN
.. autofunction:: cvc5_z3py_compat.fpPlusInfinity
.. autofunction:: cvc5_z3py_compat.fpMinusInfinity
.. autofunction:: cvc5_z3py_compat.fpInfinity
.. autofunction:: cvc5_z3py_compat.fpPlusZero
.. autofunction:: cvc5_z3py_compat.fpMinusZero
.. autofunction:: cvc5_z3py_compat.fpZero
.. autofunction:: cvc5_z3py_compat.FPSort
.. autofunction:: cvc5_z3py_compat.Float16
.. autofunction:: cvc5_z3py_compat.FloatHalf
.. autofunction:: cvc5_z3py_compat.Float32
.. autofunction:: cvc5_z3py_compat.FloatSingle
.. autofunction:: cvc5_z3py_compat.Float64
.. autofunction:: cvc5_z3py_compat.FloatDouble
.. autofunction:: cvc5_z3py_compat.Float128
.. autofunction:: cvc5_z3py_compat.FloatQuadruple

FP Operators
-------------------

See the following operator overloads for building basic floating-point terms:

* ``+``: :py:meth:`cvc5_z3py_compat.FPRef.__add__`
* ``-``: :py:meth:`cvc5_z3py_compat.FPRef.__sub__`
* ``*``: :py:meth:`cvc5_z3py_compat.FPRef.__mul__`
* unary ``-``: :py:meth:`cvc5_z3py_compat.FPRef.__neg__`
* ``/``: :py:meth:`cvc5_z3py_compat.FPRef.__div__`
* ``%``: :py:meth:`cvc5_z3py_compat.FPRef.__mod__`
* ``<=``: :py:meth:`cvc5_z3py_compat.FPRef.__le__`
* ``<``: :py:meth:`cvc5_z3py_compat.FPRef.__lt__`
* ``>=``: :py:meth:`cvc5_z3py_compat.FPRef.__ge__`
* ``>``: :py:meth:`cvc5_z3py_compat.FPRef.__gt__`

.. autofunction:: cvc5_z3py_compat.fpAbs
.. autofunction:: cvc5_z3py_compat.fpNeg
.. autofunction:: cvc5_z3py_compat.fpAdd
.. autofunction:: cvc5_z3py_compat.fpSub
.. autofunction:: cvc5_z3py_compat.fpMul
.. autofunction:: cvc5_z3py_compat.fpDiv
.. autofunction:: cvc5_z3py_compat.fpRem
.. autofunction:: cvc5_z3py_compat.fpMin
.. autofunction:: cvc5_z3py_compat.fpMax
.. autofunction:: cvc5_z3py_compat.fpFMA
.. autofunction:: cvc5_z3py_compat.fpSqrt
.. autofunction:: cvc5_z3py_compat.fpRoundToIntegral
.. autofunction:: cvc5_z3py_compat.fpIsNaN
.. autofunction:: cvc5_z3py_compat.fpIsInf
.. autofunction:: cvc5_z3py_compat.fpIsZero
.. autofunction:: cvc5_z3py_compat.fpIsNormal
.. autofunction:: cvc5_z3py_compat.fpIsSubnormal
.. autofunction:: cvc5_z3py_compat.fpIsNegative
.. autofunction:: cvc5_z3py_compat.fpIsPositive
.. autofunction:: cvc5_z3py_compat.fpLT
.. autofunction:: cvc5_z3py_compat.fpLEQ
.. autofunction:: cvc5_z3py_compat.fpGT
.. autofunction:: cvc5_z3py_compat.fpGEQ
.. autofunction:: cvc5_z3py_compat.fpEQ
.. autofunction:: cvc5_z3py_compat.fpNEQ
.. autofunction:: cvc5_z3py_compat.fpFP
.. autofunction:: cvc5_z3py_compat.fpToFP
.. autofunction:: cvc5_z3py_compat.fpBVToFP
.. autofunction:: cvc5_z3py_compat.fpFPToFP
.. autofunction:: cvc5_z3py_compat.fpRealToFP
.. autofunction:: cvc5_z3py_compat.fpSignedToFP
.. autofunction:: cvc5_z3py_compat.fpUnsignedToFP
.. autofunction:: cvc5_z3py_compat.fpToFPUnsigned
.. autofunction:: cvc5_z3py_compat.fpToSBV
.. autofunction:: cvc5_z3py_compat.fpToUBV
.. autofunction:: cvc5_z3py_compat.fpToReal



Testers
-------------------
.. autofunction:: cvc5_z3py_compat.is_fp_sort
.. autofunction:: cvc5_z3py_compat.is_fp
.. autofunction:: cvc5_z3py_compat.is_fp_value
.. autofunction:: cvc5_z3py_compat.is_fprm_sort
.. autofunction:: cvc5_z3py_compat.is_fprm
.. autofunction:: cvc5_z3py_compat.is_fprm_value


FP Rounding Modes
-------------------------
.. autofunction:: cvc5_z3py_compat.RoundNearestTiesToEven
.. autofunction:: cvc5_z3py_compat.RNE
.. autofunction:: cvc5_z3py_compat.RoundNearestTiesToAway
.. autofunction:: cvc5_z3py_compat.RNA
.. autofunction:: cvc5_z3py_compat.RoundTowardPositive
.. autofunction:: cvc5_z3py_compat.RTP
.. autofunction:: cvc5_z3py_compat.RoundTowardNegative
.. autofunction:: cvc5_z3py_compat.RTN
.. autofunction:: cvc5_z3py_compat.RoundTowardZero
.. autofunction:: cvc5_z3py_compat.RTZ
.. autofunction:: cvc5_z3py_compat.get_default_rounding_mode
.. autofunction:: cvc5_z3py_compat.set_default_rounding_mode
.. autofunction:: cvc5_z3py_compat.get_default_fp_sort
.. autofunction:: cvc5_z3py_compat.set_default_fp_sort


Classes (with overloads)
------------------------

.. autoclass:: cvc5_z3py_compat.FPSortRef
  :members:
  :special-members:
.. autoclass:: cvc5_z3py_compat.FPRef
  :members:
  :special-members:
.. autoclass:: cvc5_z3py_compat.FPNumRef
  :members:
  :special-members:
.. autoclass:: cvc5_z3py_compat.FPRMRef
  :members:
  :special-members:


