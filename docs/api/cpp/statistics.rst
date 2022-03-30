Statistics
==========

See :doc:`/statistics` for general information on statistics in cvc5..
The :cpp:class:`Statistics <cvc5::api::Statistics>` object is essentially a
mapping from names (as ``std::string``) to statistic values, represented by the
:cpp:class:`Stat <cvc5::api::Stat>` class. A :cpp:class:`Stat <cvc5::api::Stat>`
can hold values of different types (``int64_t``, ``double``, ``std::string`` and
histograms) and can be inspected by identifying the type
(:cpp:func:`Stat::isInt() <cvc5::api::Stat::isInt()>`,
:cpp:func:`Stat::isDouble() <cvc5::api::Stat::isDouble()>`, etc) and obtaining
the actual value (:cpp:func:`Stat::getInt() <cvc5::api::Stat::getInt()>`,
:cpp:func:`Stat::getDouble() <cvc5::api::Stat::getDouble()>`, etc). Histograms
are represented as ``std::map<std::string, uint64_t>`` where the key is the strings representation of one enumeration value
and the value is the frequency of this particular value.

By default, iterating a
:cpp:class:`Statistics <cvc5::api::Statistics>` object only shows statistics
that are both public and changed. The :cpp:func:`Statistics::begin()
<cvc5::api::Statistics::begin()>` method has Boolean flags ``internal`` and
``def`` to also show internal statistics and defaulted statistics, respectively.


.. doxygenclass:: cvc5::api::Statistics
    :project: cvc5
    :members: get, begin, end
    :undoc-members:

.. doxygenclass:: cvc5::api::Stat
    :project: cvc5
    :members:
    :undoc-members:
