Options
=======

cvc5 can be configured at runtime using a wide range of options that can be set using the command line when cvc5 is used as a binary, or the :cpp:func:`Solver::setOption() <cvc5::api::Solver::setOption()>` API function.
When using the API, options can also be inspected using :cpp:func:`Solver::getOption() <cvc5::api::Solver::getOption()>`, :cpp:func:`Solver::getOptionNames() <cvc5::api::Solver::getOptionNames()>`, and :cpp:func:`Solver::getOptionInfo() <cvc5::api::Solver::getOptionInfo()>`.

All options have a `long name` that is used as identifier for this option in all API functions and in the input languages. For the command line, options are specified as ``--<long name>``, and for (most) Boolean options the inverse flag ``--no-<long-name>`` is supported as well.
Below is an exhaustive list of options supported by cvc5.

.. include-build-file:: options_generated.rst
