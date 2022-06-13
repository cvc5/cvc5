Options
=======

cvc5 can be configured at runtime using a wide range of options.
When cvc5 is used as a binary, options can be set on the command line.
Also, options can be set and inspected using the respective commands of the input language and the corresponding API functions:

- C++ API: :cpp:func:`setOption() <cvc5::Solver::setOption()>`,
  :cpp:func:`getOption() <cvc5::Solver::getOption()>`,
  :cpp:func:`getOptionNames() <cvc5::Solver::getOptionNames()>`,
  :cpp:func:`getOptionInfo() <cvc5::Solver::getOptionInfo()>`
- Java API: ``setOption()``, ``getOption()``, ``getOptionNames()``, ``getOptionInfo()``
- Base Python API: :py:func:`setOption() <cvc5.Solver.setOption()>`,
  :py:func:`getOption() <cvc5.Solver.getOption()>`,
  :py:func:`getOptionNames() <cvc5.Solver.getOptionNames()>`,
  :py:func:`getOptionInfo() <cvc5.Solver.getOptionInfo()>`
- Pythonic API: :py:func:`setOption() <cvc5.pythonic.Solver.setOption()>`,
  :py:func:`getOption() <cvc5.pythonic.Solver.getOption()>`,
  :py:func:`getOptionNames() <cvc5.pythonic.Solver.getOptionNames()>`,
  :py:func:`getOptionInfo() <cvc5.pythonic.Solver.getOptionInfo()>`

Generally, all options are identified by a name ``<name>``, and (optionally)
by a short name ``<short>`` (a single letter).
Additionally, they can have one or more aliases, which can be used instead of
``<name>``.

**Internally**, options are strongly typed and must be either Boolean, (signed
or unsigned) integers, floating-point numbers, strings, or an enumeration type.
Values for options with a numeric type may be restricted to an interval.

Some options have **custom types** (e.g., :ref:`err <lbl-option-err>`) which
require special treatment internally.
The usage of such options is documented as part of the documentation for the corresponding options.

On the command line, a **Boolean** option can be set to ``true`` via
``--<name>`` or ``-<short>``.
Most Boolean options can also be set to ``false`` via ``--no-<name>``.
In cvc5's APIs, this is done via ``setOption("<name>", "true" | "false")``.

For **all other types**, values are given on the command line using
``--<name>=<value>`` or ``--<name> <value>``,
and ``setOption("<name>", "<value>")`` in the APIs.
The given value must be convertible to the appropriate type, in particular for
numeric and enumeration types.

Below is an exhaustive list of options supported by cvc5.

.. include-build-file:: options_generated.rst
