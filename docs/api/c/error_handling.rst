Error handling
==============

Unlike the C++ API, which reports errors by throwing exceptions, the C API
cannot propagate exceptions across the language boundary. Instead of
terminating the process when an error occurs, cvc5 C API functions record the
error in **thread-local** state and return a default value (e.g., ``NULL``,
``false``, or ``0``).

After invoking a C API function, the caller can check whether it succeeded via
:cpp:func:`cvc5_has_error()` and retrieve the associated message via
:cpp:func:`cvc5_get_error_message()`. The error state is reset at the beginning
of each C API call, so it always reflects the outcome of the most recent call.
For example:

.. code:: c

   Cvc5TermManager* tm = cvc5_term_manager_new();
   Cvc5* cvc5 = cvc5_new(tm);
   // Trigger an error by passing an invalid (NULL) argument.
   cvc5_assert_formula(cvc5, NULL);
   if (cvc5_has_error())
   {
     fprintf(stderr, "cvc5 error: %s\n", cvc5_get_error_message());
   }
   cvc5_delete(cvc5);
   cvc5_term_manager_delete(tm);

.. container:: hide-toctree

  .. toctree::

----

.. doxygengroup:: c_error_handling
    :project: cvc5_c
    :content-only:
