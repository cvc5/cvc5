Core & Booleans
================

Basic Boolean Term Builders
---------------------------
.. autofunction:: cvc5_z3py_compat.Bool
.. autofunction:: cvc5_z3py_compat.BoolVal
.. autofunction:: cvc5_z3py_compat.BoolSort
.. autofunction:: cvc5_z3py_compat.FreshBool
.. autofunction:: cvc5_z3py_compat.Bools
.. autofunction:: cvc5_z3py_compat.BoolVector

Basic Generic Term Builders
---------------------------
.. autofunction:: cvc5_z3py_compat.Const
.. autofunction:: cvc5_z3py_compat.Consts
.. autofunction:: cvc5_z3py_compat.FreshConst
.. autofunction:: cvc5_z3py_compat.Function
.. autofunction:: cvc5_z3py_compat.FreshFunction

Boolean Operators
-----------------
.. autofunction:: cvc5_z3py_compat.And
.. autofunction:: cvc5_z3py_compat.Or
.. autofunction:: cvc5_z3py_compat.Not
.. autofunction:: cvc5_z3py_compat.mk_not
.. autofunction:: cvc5_z3py_compat.Implies
.. autofunction:: cvc5_z3py_compat.Xor

Generic Operators
-----------------
.. autofunction:: cvc5_z3py_compat.If
.. autofunction:: cvc5_z3py_compat.Distinct

Equality
~~~~~~~~

See
:py:meth:`cvc5_z3py_compat.ExprRef.__eq__`
and
:py:meth:`cvc5_z3py_compat.ExprRef.__ne__`
for building equality and disequality terms.


Testers
-------
.. autofunction:: cvc5_z3py_compat.is_bool
.. autofunction:: cvc5_z3py_compat.is_bool_value
.. autofunction:: cvc5_z3py_compat.is_true
.. autofunction:: cvc5_z3py_compat.is_false
.. autofunction:: cvc5_z3py_compat.is_and
.. autofunction:: cvc5_z3py_compat.is_or
.. autofunction:: cvc5_z3py_compat.is_implies
.. autofunction:: cvc5_z3py_compat.is_not
.. autofunction:: cvc5_z3py_compat.is_eq
.. autofunction:: cvc5_z3py_compat.is_distinct
.. autofunction:: cvc5_z3py_compat.is_const
.. autofunction:: cvc5_z3py_compat.is_func_decl


Classes (with overloads)
----------------------------
.. autoclass:: cvc5_z3py_compat.ExprRef
   :members:
   :special-members:
.. autoclass:: cvc5_z3py_compat.SortRef
   :members:
   :special-members:
.. autoclass:: cvc5_z3py_compat.BoolRef
   :members:
   :special-members:
.. autoclass:: cvc5_z3py_compat.BoolSortRef
   :members:
   :special-members:
.. autoclass:: cvc5_z3py_compat.FuncDeclRef
   :members:
   :special-members:
