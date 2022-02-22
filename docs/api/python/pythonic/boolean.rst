Core & Booleans
================

Basic Boolean Term Builders
---------------------------
.. autofunction:: cvc5.pythonic.Bool
.. autofunction:: cvc5.pythonic.BoolVal
.. autofunction:: cvc5.pythonic.BoolSort
.. autofunction:: cvc5.pythonic.FreshBool
.. autofunction:: cvc5.pythonic.Bools
.. autofunction:: cvc5.pythonic.BoolVector

Basic Generic Term Builders
---------------------------
.. autofunction:: cvc5.pythonic.Const
.. autofunction:: cvc5.pythonic.Consts
.. autofunction:: cvc5.pythonic.FreshConst
.. autofunction:: cvc5.pythonic.Function
.. autofunction:: cvc5.pythonic.FreshFunction

Boolean Operators
-----------------
.. autofunction:: cvc5.pythonic.And
.. autofunction:: cvc5.pythonic.Or
.. autofunction:: cvc5.pythonic.Not
.. autofunction:: cvc5.pythonic.mk_not
.. autofunction:: cvc5.pythonic.Implies
.. autofunction:: cvc5.pythonic.Xor

Generic Operators
-----------------
.. autofunction:: cvc5.pythonic.If
.. autofunction:: cvc5.pythonic.Distinct

Equality
~~~~~~~~

See
:py:meth:`cvc5.pythonic.ExprRef.__eq__`
and
:py:meth:`cvc5.pythonic.ExprRef.__ne__`
for building equality and disequality terms.


Testers
-------
.. autofunction:: cvc5.pythonic.is_bool
.. autofunction:: cvc5.pythonic.is_bool_value
.. autofunction:: cvc5.pythonic.is_true
.. autofunction:: cvc5.pythonic.is_false
.. autofunction:: cvc5.pythonic.is_and
.. autofunction:: cvc5.pythonic.is_or
.. autofunction:: cvc5.pythonic.is_implies
.. autofunction:: cvc5.pythonic.is_not
.. autofunction:: cvc5.pythonic.is_eq
.. autofunction:: cvc5.pythonic.is_distinct
.. autofunction:: cvc5.pythonic.is_const
.. autofunction:: cvc5.pythonic.is_func_decl


Classes (with overloads)
----------------------------
.. autoclass:: cvc5.pythonic.ExprRef
   :members:
   :special-members:
.. autoclass:: cvc5.pythonic.SortRef
   :members:
   :special-members:
.. autoclass:: cvc5.pythonic.BoolRef
   :members:
   :special-members:
.. autoclass:: cvc5.pythonic.BoolSortRef
   :members:
   :special-members:
.. autoclass:: cvc5.pythonic.FuncDeclRef
   :members:
   :special-members:
