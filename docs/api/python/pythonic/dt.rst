Datatypes
============

Overview
----------

To manipulate instances of a datatype, one must first *declare* the datatype itself.
Declaration happens in three phases. Let's consider declaring a cons-list of
integers.

First, we initialize the datatype with its *name*

    >>> IntList = Datatype('IntList')

Second, we declare constructors for the datatype, giving the *constructor name*
and *field names and sorts*. Here is the empty list constructor:

    >>> IntList.declare('nil', ())

Here is the cons constructor:

    >>> IntList.declare('cons', ('val', IntSort()), ('tail', IntList))

Third, after all constructors are declared, we can *create* the datatype,
finishing its declaration.

    >>> IntList = IntList.create()

Now, one has access to a number of tools for interacting with integer lists.

* ``IntList.nil`` refers to the SMT term that is an empty list,
  and ``IntList.cons`` refers to the cons constructor.
* ``IntList.is_nil`` and ``IntList.is_cons`` are testors (a.k.a.,
  recognizers) for those constructors.
* ``IntList.val`` and ``IntList.tail`` are selectors (a.k.a. accessors)
  for the cons constructor.

If constructor, accessor, or selector names are ambiguous (e.g., if different
constructors have selectors of the same name), then see the methods on
:py:class:`cvc5.pythonic.DatatypeSortRef` to unambiguously access a specific
function.

To create mutually recursive datatypes, see
:py:func:`cvc5.pythonic.CreateDatatypes`.

To create a codataype (e.g., a possibly infinite stream of integers), pass the
``isCoDatatype=True`` argument to the :py:class:`cvc5.pythonic.Datatype`
constructor.

    >>> IntStream = Datatype('IntStream', isCoDatatype=True)

Declaration Utilities
---------------------

.. autofunction:: cvc5.pythonic.CreateDatatypes
.. autofunction:: cvc5.pythonic.TupleSort
.. autofunction:: cvc5.pythonic.DisjointSum


Classes
------------------------
.. autoclass:: cvc5.pythonic.Datatype
  :members:
  :special-members:
.. autoclass:: cvc5.pythonic.DatatypeSortRef
  :members:
  :special-members:
.. autoclass:: cvc5.pythonic.DatatypeConstructorRef
  :members:
  :special-members:
.. autoclass:: cvc5.pythonic.DatatypeSelectorRef
  :members:
  :special-members:
.. autoclass:: cvc5.pythonic.DatatypeRecognizerRef
  :members:
  :special-members:
.. autoclass:: cvc5.pythonic.DatatypeRef
  :members:
  :special-members:
