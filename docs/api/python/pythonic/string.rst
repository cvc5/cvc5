Strings
============


Basic Sequence Term Builders
------------------------------

.. autofunction:: cvc5.pythonic.StringSort
.. autofunction:: cvc5.pythonic.String
.. autofunction:: cvc5.pythonic.Strings
.. autofunction:: cvc5.pythonic.StringVal

String Operators
-------------------

.. autofunction:: cvc5.pythonic.Length
.. autofunction:: cvc5.pythonic.SubString
.. autofunction:: cvc5.pythonic.Contains
.. autofunction:: cvc5.pythonic.PrefixOf
.. autofunction:: cvc5.pythonic.SuffixOf
.. autofunction:: cvc5.pythonic.IndexOf
.. autofunction:: cvc5.pythonic.Replace
.. autofunction:: cvc5.pythonic.StrToInt
.. autofunction:: cvc5.pythonic.IntToStr
.. autofunction:: cvc5.pythonic.StrToCode
.. autofunction:: cvc5.pythonic.StrFromCode

Basic Regular Expression Term Builders
---------------------------------------
.. autofunction:: cvc5.pythonic.Re
.. autofunction:: cvc5.pythonic.Full
.. autofunction:: cvc5.pythonic.Option
.. autofunction:: cvc5.pythonic.Range
.. autofunction:: cvc5.pythonic.AllChar


Regular Expression Operators
-----------------------------
.. autofunction:: cvc5.pythonic.InRe
.. autofunction:: cvc5.pythonic.Union
.. autofunction:: cvc5.pythonic.Intersect
.. autofunction:: cvc5.pythonic.Complement
.. autofunction:: cvc5.pythonic.Plus
.. autofunction:: cvc5.pythonic.Star
.. autofunction:: cvc5.pythonic.Loop
.. autofunction:: cvc5.pythonic.Diff


See the following operator overload for string terms:

* is member: :py:meth:`cvc5.pythonic.StringRef.__getitem__`


Classes (with overloads)
------------------------

.. autoclass:: cvc5.pythonic.StringSortRef
  :members:
  :special-members:
.. autoclass:: cvc5.pythonic.StringRef
  :members:
  :special-members:
