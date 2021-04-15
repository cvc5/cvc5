Statistics
==========

The solver collects a variety of statistics that can be helpful in
understanding what the solver is doing internally.
The entirety of collected statistics are represented by a :cpp:class:`Statistics <cvc5::api::Statistics>` object
that can be obtained from :cpp:func:`Solver::getStatistics() <cvc5::api::Solver::getStatistics>`. It is a copy of the
internal solver statistics at this point in time.

The `Statistics` object is essentially a mapping from names (as ``std::string``)
to statistic values, represented by the :cpp:class:`Stat <cvc5::api::Stat>` class. A :cpp:class:`Stat <cvc5::api::Stat>` can hold values
of different types and can be inspected by identifying the type
(:cpp:func:`Stat::isInt() <cvc5::api::Stat::isInt()>`, :cpp:func:`Stat::isDouble() <cvc5::api::Stat::isDouble()>`, etc) and obtaining the actual value
(:cpp:func:`Stat::getInt() <cvc5::api::Stat::getInt()>`, :cpp:func:`Stat::getDouble() <cvc5::api::Stat::getDouble()>`, etc).

Statistics are generally categorized into public and expert statistics, and
furthermore into changed and defaulted statistics. By default, iterating a
:cpp:class:`Statistics <cvc5::api::Statistics>` object only shows statistics that are both public and changed.
The :cpp:func:`Statistics::begin() <cvc5::api::Statistics::begin()>` method has Boolean flags ``expert`` and ``def`` to also
show expert statistics and defaulted statistics, respectively.

.. doxygenclass:: cvc5::api::Statistics
    :project: cvc5
    :members:
    :undoc-members:

.. doxygenclass:: cvc5::api::Stat
    :project: cvc5
    :members:
    :undoc-members:
