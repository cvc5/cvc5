Cvc5OptionInfo
==============

This struct encapsulates all the information associated with a configuration
option. It can be retrieved via :cpp:func:`cvc5_get_option_info()`
and allows to query any configuration information associated with an option.

The kind of an option info object is defined as enum
:cpp:enum:`Cvc5OptionInfoKind`. Encapsulated values can be queried depending on
the kind.

.. container:: hide-toctree

  .. toctree::

----

.. doxygenenum:: Cvc5OptionInfoKind
    :project: cvc5_c

----

.. The following directive triggers a spurious warning. See issues:
   https://github.com/breathe-doc/breathe/issues/543
   https://github.com/sphinx-doc/sphinx/issues/7819
   As a workaround, we add a note in the Cvc5OptionInfo struct documentation.

   .. doxygentypedef:: Cvc5OptionInfo
      :project: cvc5_c

.. doxygenstruct:: Cvc5OptionInfo
    :project: cvc5_c
    :members:

----

.. doxygengroup:: c_cvc5optioninfo
    :project: cvc5_c
    :content-only:
