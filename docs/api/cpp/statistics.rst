Statistics
==========

See :doc:`/statistics` for general information on statistics in cvc5.

Class :cpp:class:`cvc5::Statistics` represents a mapping from statistic names
(as ``std::string``) to statistic values, which are represented by class
:cpp:class:`cvc5::Stat`. A :cpp:class:`cvc5::Stat` may hold values of different
types (``int64_t``, ``double``, ``std::string`` and histograms) and can be
inspected by identifying the type
(:cpp:func:`Stat::isInt() <cvc5::Stat::isInt()>`,
:cpp:func:`Stat::isDouble() <cvc5::Stat::isDouble()>`, etc) and obtaining
the actual value (:cpp:func:`Stat::getInt() <cvc5::Stat::getInt()>`,
:cpp:func:`Stat::getDouble() <cvc5::Stat::getDouble()>`, etc). Histograms
are represented as ``std::map<std::string, uint64_t>`` where the key is the
string representation of one enumeration value
and the value is the frequency of this particular value.

By default, iterating over a :cpp:class:`Statistics <cvc5::Statistics>`
object shows all statistics, including internal and unchanged ones.
The inclusion of internal and defaulted statistics can be configured via
Boolean parameters ``internal`` and ``defaulted`` of function
:cpp:func:`Statistics::begin() <cvc5::Statistics::begin()>`.

----

- class :cpp:class:`cvc5::Statistics`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const Statistics& s)`
- class :cpp:class:`cvc5::Stat`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const Stat& s)`

----

.. doxygenclass:: cvc5::Statistics
    :project: cvc5
    :members: get, begin, end
    :undoc-members:

----

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const Statistics& s)
    :project: cvc5

----

.. doxygenclass:: cvc5::Stat
    :project: cvc5
    :members:
    :undoc-members:

----

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const Stat& s)
    :project: cvc5

