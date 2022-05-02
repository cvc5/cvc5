Floating Point
==============

Basic FP Term Builders
-------------------------

.. autofunction:: cvc5.pythonic.FP
.. autofunction:: cvc5.pythonic.FPs
.. autofunction:: cvc5.pythonic.FPVal
.. autofunction:: cvc5.pythonic.fpNaN
.. autofunction:: cvc5.pythonic.fpPlusInfinity
.. autofunction:: cvc5.pythonic.fpMinusInfinity
.. autofunction:: cvc5.pythonic.fpInfinity
.. autofunction:: cvc5.pythonic.fpPlusZero
.. autofunction:: cvc5.pythonic.fpMinusZero
.. autofunction:: cvc5.pythonic.fpZero
.. autofunction:: cvc5.pythonic.FPSort
.. autofunction:: cvc5.pythonic.Float16
.. autofunction:: cvc5.pythonic.FloatHalf
.. autofunction:: cvc5.pythonic.Float32
.. autofunction:: cvc5.pythonic.FloatSingle
.. autofunction:: cvc5.pythonic.Float64
.. autofunction:: cvc5.pythonic.FloatDouble
.. autofunction:: cvc5.pythonic.Float128
.. autofunction:: cvc5.pythonic.FloatQuadruple

FP Operators
-------------------

See the following operator overloads for building basic floating-point terms:

* ``+``: :py:meth:`cvc5.pythonic.FPRef.__add__`
* ``-``: :py:meth:`cvc5.pythonic.FPRef.__sub__`
* ``*``: :py:meth:`cvc5.pythonic.FPRef.__mul__`
* unary ``-``: :py:meth:`cvc5.pythonic.FPRef.__neg__`
* ``/``: :py:meth:`cvc5.pythonic.FPRef.__div__`
* ``%``: :py:meth:`cvc5.pythonic.FPRef.__mod__`
* ``<=``: :py:meth:`cvc5.pythonic.FPRef.__le__`
* ``<``: :py:meth:`cvc5.pythonic.FPRef.__lt__`
* ``>=``: :py:meth:`cvc5.pythonic.FPRef.__ge__`
* ``>``: :py:meth:`cvc5.pythonic.FPRef.__gt__`

.. autofunction:: cvc5.pythonic.fpAbs
.. autofunction:: cvc5.pythonic.fpNeg
.. autofunction:: cvc5.pythonic.fpAdd
.. autofunction:: cvc5.pythonic.fpSub
.. autofunction:: cvc5.pythonic.fpMul
.. autofunction:: cvc5.pythonic.fpDiv
.. autofunction:: cvc5.pythonic.fpRem
.. autofunction:: cvc5.pythonic.fpMin
.. autofunction:: cvc5.pythonic.fpMax
.. autofunction:: cvc5.pythonic.fpFMA
.. autofunction:: cvc5.pythonic.fpSqrt
.. autofunction:: cvc5.pythonic.fpRoundToIntegral
.. autofunction:: cvc5.pythonic.fpIsNaN
.. autofunction:: cvc5.pythonic.fpIsInf
.. autofunction:: cvc5.pythonic.fpIsZero
.. autofunction:: cvc5.pythonic.fpIsNormal
.. autofunction:: cvc5.pythonic.fpIsSubnormal
.. autofunction:: cvc5.pythonic.fpIsNegative
.. autofunction:: cvc5.pythonic.fpIsPositive
.. autofunction:: cvc5.pythonic.fpLT
.. autofunction:: cvc5.pythonic.fpLEQ
.. autofunction:: cvc5.pythonic.fpGT
.. autofunction:: cvc5.pythonic.fpGEQ
.. autofunction:: cvc5.pythonic.fpEQ
.. autofunction:: cvc5.pythonic.fpNEQ
.. autofunction:: cvc5.pythonic.fpFP
.. autofunction:: cvc5.pythonic.fpToFP
.. autofunction:: cvc5.pythonic.fpBVToFP
.. autofunction:: cvc5.pythonic.fpFPToFP
.. autofunction:: cvc5.pythonic.fpRealToFP
.. autofunction:: cvc5.pythonic.fpSignedToFP
.. autofunction:: cvc5.pythonic.fpUnsignedToFP
.. autofunction:: cvc5.pythonic.fpToFPUnsigned
.. autofunction:: cvc5.pythonic.fpToSBV
.. autofunction:: cvc5.pythonic.fpToUBV
.. autofunction:: cvc5.pythonic.fpToReal



Testers
-------------------
.. autofunction:: cvc5.pythonic.is_fp_sort
.. autofunction:: cvc5.pythonic.is_fp
.. autofunction:: cvc5.pythonic.is_fp_value
.. autofunction:: cvc5.pythonic.is_fprm_sort
.. autofunction:: cvc5.pythonic.is_fprm
.. autofunction:: cvc5.pythonic.is_fprm_value


FP Rounding Modes
-------------------------
.. autofunction:: cvc5.pythonic.RoundNearestTiesToEven
.. autofunction:: cvc5.pythonic.RNE
.. autofunction:: cvc5.pythonic.RoundNearestTiesToAway
.. autofunction:: cvc5.pythonic.RNA
.. autofunction:: cvc5.pythonic.RoundTowardPositive
.. autofunction:: cvc5.pythonic.RTP
.. autofunction:: cvc5.pythonic.RoundTowardNegative
.. autofunction:: cvc5.pythonic.RTN
.. autofunction:: cvc5.pythonic.RoundTowardZero
.. autofunction:: cvc5.pythonic.RTZ
.. autofunction:: cvc5.pythonic.get_default_rounding_mode
.. autofunction:: cvc5.pythonic.set_default_rounding_mode
.. autofunction:: cvc5.pythonic.get_default_fp_sort
.. autofunction:: cvc5.pythonic.set_default_fp_sort


Classes (with overloads)
------------------------

.. autoclass:: cvc5.pythonic.FPSortRef
  :members:
  :special-members:
.. autoclass:: cvc5.pythonic.FPRef
  :members:
  :special-members:
.. autoclass:: cvc5.pythonic.FPNumRef
  :members:
  :special-members:
.. autoclass:: cvc5.pythonic.FPRMRef
  :members:
  :special-members:


