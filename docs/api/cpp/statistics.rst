Statistics
==========

The solver collects a variety of statistics that can be helpful in understanding
what the solver is doing internally. The entirety of collected statistics are
represented by a :cpp:class:`Statistics <cvc5::Statistics>` object that can
be obtained from :cpp:func:`Solver::getStatistics()
<cvc5::Solver::getStatistics>`. It is a copy of the internal solver
statistics at this point in time.

The :cpp:class:`Statistics <cvc5::Statistics>` object is essentially a
mapping from names (as ``std::string``) to statistic values, represented by the
:cpp:class:`Stat <cvc5::Stat>` class. A :cpp:class:`Stat <cvc5::Stat>`
can hold values of different types (``int64_t``, ``double``, ``std::string`` and
histograms) and can be inspected by identifying the type
(:cpp:func:`Stat::isInt() <cvc5::Stat::isInt()>`,
:cpp:func:`Stat::isDouble() <cvc5::Stat::isDouble()>`, etc) and obtaining
the actual value (:cpp:func:`Stat::getInt() <cvc5::Stat::getInt()>`,
:cpp:func:`Stat::getDouble() <cvc5::Stat::getDouble()>`, etc). Histograms
conceptually count the frequency of different values of an arbitrary type,
usually an enumeration type. They are represented as ``std::map<std::string,
uint64_t>`` where the key is the strings representation of one enumeration value
and the value is the frequency of this particular value.

Statistics are generally categorized into public and internal statistics, and
furthermore into changed and defaulted statistics. By default, iterating a
:cpp:class:`Statistics <cvc5::Statistics>` object only shows statistics
that are both public and changed. The :cpp:func:`Statistics::begin()
<cvc5::Statistics::begin()>` method has Boolean flags ``internal`` and
``def`` to also show internal statistics and defaulted statistics, respectively.


.. doxygenclass:: cvc5::Statistics
    :project: cvc5
    :members: get, begin, end
    :undoc-members:

.. doxygenclass:: cvc5::Stat
    :project: cvc5
    :members:
    :undoc-members:
