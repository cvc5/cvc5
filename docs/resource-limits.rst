Resource limits
===============

cvc5 supports limiting the time or *resources* it uses during solving via the options
:ref:`tlimit <lbl-option-tlimit>`, :ref:`tlimit-per <lbl-option-tlimit-per>`,
:ref:`rlimit <lbl-option-rlimit>`, and :ref:`rlimit-per <lbl-option-rlimit-per>`.
All these options take a single non-negative number as an argument where giving zero explicitly disables the respective limit. For time limits the number is interpreted as the number of milliseconds, and for resource limits it indicates the amount of *resources*.

The limits configured using :ref:`tlimit <lbl-option-tlimit>` and :ref:`rlimit <lbl-option-rlimit>` restrict time and resource usage over the whole lifetime of the :cpp:class:`solver <cvc5::Solver>` object, respectively.
In contrast to that, :ref:`tlimit-per <lbl-option-tlimit-per>` and :ref:`rlimit-per <lbl-option-rlimit-per>` apply to every check individually (:cpp:func:`checkSat <cvc5::Solver::checkSat>`, :cpp:func:`checkSatAssuming <cvc5::Solver::checkSatAssuming>`, etc).

Except for the overall time limit (see below), the limits are checked by cvc5 itself. This means that the solver remains in a safe state after a limit has been reached.
Due to the way cvc5 checks these limits (see below), cvc5 may not precisely honor per-call time limits: if a subroutine requires a long time to finish without spending resources itself, cvc5 only realizes afterwards that the timeout has (long) passed.


Overall time limit (:ref:`tlimit <lbl-option-tlimit>` option)
-------------------------------------------------------------

The :ref:`tlimit <lbl-option-tlimit>` option limits the overall running time of the cvc5 solver binary.
It is implemented using an asynchronous interrupt that is usually managed by the operating system (using ``setitimer``).
When this interrupt occurs, cvc5 outputs a corresponding message, prints the current statistics and immediately terminates its process. The same is done when an external resource limiting mechanism is in place, for example ``ulimit``.

This mechanism is inherently unsuited when cvc5 is used within another application process via one of its APIs: therefore, it is only honored when running as a standalone binary.
Setting :ref:`tlimit <lbl-option-tlimit>` via the API or the ``(set-option)`` SMT-LIB command has thus no effect.


Resource manager and resource spending
--------------------------------------

All other limits are enforced centrally by the resource manager as follows.
Whenever certain parts of the solver execute, they instruct the resource manager to *spend* a resource.
As soon as the resource manager realizes that some limit is exhausted (either the resource limit or the per-check time limit is reached), it asynchronously instructs the core solver to interrupt the check.
To not invalidate the internal state of the solver, and allow to use it again after an interrupt, the solver continues its work until it reaches a safe point in one of the core solving components.
Then, it returns `unknown` (with an :cpp:enum:`explanation <cvc5::UnknownExplanation>`).

The intention of a resource limit is to be a deterministic measure that grows (linearly, if possible) with actual running time.
Resources are spent when lemmas are generated and during a few select events like preprocessing, rewriting, decisions and restarts in the SAT solver, or theory checks.
In case the resource spending does not properly reflect the running time, the weights of the individual resources can be modified using the :ref:`rweight <lbl-option-rweight>` option, for example with ``--rweight=RestartStep=5``.
