Statistics
==========

cvc5 collects a wide variety of statistics that give some insight on how it solves a particular input.
The statistics can be inspected via the :cpp:func:`Solver::getStatistics() <cvc5::Solver::getStatistics()>` API
function, or printed using the following options:

- :ref:`stats <lbl-option-stats>` prints public statistics with non-default values
- :ref:`stats-all <lbl-option-stats-all>` also prints statistics with default values
- :ref:`stats-internal <lbl-option-stats-internal>` also prints internal statistics
- :ref:`stats-every-query <lbl-option-stats-every-query>` prints statistics after every (incremental) check

Statistics collection is only available if the ``ENABLE_STATISTICS`` cmake option
is set to true, which is the case for all but competition builds.
Statistics, obtained via :cpp:func:`Solver::getStatistics() <cvc5::Solver::getStatistics()>`,
are always a snapshot of the statistics values that is decoupled from the
solver object and will not change when the solver is used again or deallocated.
Individual statistics values can be obtained via the API either by iterating over the 
:cpp:class:`Statistics <cvc5::Statistics>` object or by querying it by name.

A statistic value (of type :cpp:class:`Stat <cvc5::Stat>`) has two general
properties, :cpp:func:`isInternal() <cvc5::Stat::isInternal()>` and
:cpp:func:`isDefault() <cvc5::Stat::isDefault()>`.
:cpp:func:`isInternal() <cvc5::Stat::isInternal()>` indicates whether a
statistic is considered public or internal. Public statistics are considered to
be part of the public API and should therefore remain stable across different
minor versions of cvc5. There is no such guarantee for internal statistics.
:cpp:func:`isDefault() <cvc5::Stat::isDefault()>` checks whether the
current value of a statistics is still the default value, or whether its value
was changed.

A statistic value can be any of the following types:

- integer, more specifically a signed 64-bit integer (``int64_t`` in C++).
- double, a 64-bit floating-point value (``double`` in C++).
- string, a character sequence (``std::string`` in C++). Timer statistics are
  exported as string values as well, given as ``"<value>ms"``.
- histogram, a mapping from some integral or enumeration type to their count.
  The integral or enumeration types are exported as string representations
  (``std::map<std::string, uint64_t>`` in C++).

Printing statistics on the command line looks like this:

.. run-command:: bin/cvc5 --stats ../test/regress/cli/regress0/auflia/bug336.smt2

Public statistics include some general information about the input file
(``driver::filename`` and ``*``), the overall runtime (``global::totalTime``)
and the lemmas each theory sent to the core solver (``theory::*``).
