[![License: BSD](
    https://img.shields.io/badge/License-BSD%203--Clause-blue.svg)](
        https://opensource.org/licenses/BSD-3-Clause)
[![Build Status](
    https://travis-ci.org/CVC4/CVC4.svg?branch=master)](
        https://travis-ci.org/CVC4/CVC4)

CVC4
===============================================================================

CVC4 is a tool for determining the satisfiability of a first order formula
modulo a first order theory (or a combination of such theories).  It is the
fourth in the Cooperating Validity Checker family of tools (CVC, CVC Lite,
CVC3) but does not directly incorporate code from any previous version.

CVC4 is intended to be an open and extensible SMT engine.  It can be used as a
stand-alone tool or as a library.  It has been designed to increase the
performance and reduce the memory overhead of its predecessors.  It is written
entirely in C++ and is released under an open-source software license (see file
[COPYING](https://github.com/CVC4/CVC4/blob/master/COPYING)).


Website
-------------------------------------------------------------------------------

More information about CVC4 is available at:
http://cvc4.cs.stanford.edu/

Download
-------------------------------------------------------------------------------

The latest version of CVC4 is available on GitHub:
https://github.com/CVC4/CVC4

Source tar balls and binaries for releases and latest stable builds of the
[master branch](https://github.com/CVC4/CVC4) on GitHub can be
found [here](http://cvc4.cs.stanford.edu/downloads).


Build and Dependencies
-------------------------------------------------------------------------------

CVC4 can be built on Linux and macOS.  For Windows, CVC4 can be cross-compiled
using Mingw-w64.

For detailed build and installation instructions on these platforms,
see file [INSTALL.md](https://github.com/CVC4/CVC4/blob/master/INSTALL.md).


Getting Started
-------------------------------------------------------------------------------

We recommend that you visit our CVC4 tutorials online at:

  http://cvc4.cs.stanford.edu/wiki/Tutorials

for help getting started using CVC4.


Contributing
-------------------------------------------------------------------------------

We are always happy to hear feedback from our users:

* if you need help with using CVC4, please refer to
  [http://cvc4.stanford.edu/#Technical_Support](http://cvc4.stanford.edu/#Technical_Support).

* if you need to report a bug with CVC4, or make a feature request, please
  visit our bugtracker at our
  [GitHub issues](https://github.com/CVC4/CVC4/issues) page. We are very
  grateful for bug reports,  as they help us improve CVC4, and patches are
  generally reviewed and accepted quickly.

* if you are using CVC4 in your work, or incorporating it into software of your
  own, we'd like to invite you to leave a description and link to your
  project/software on our [Third Party Applications](http://cvc4.cs.stanford.edu/wiki/Public:Third_Party_Applications).

* if you are interested in contributing code (for example, a new
  decision procedure implementation) to the CVC4 project, please
  contact one of the [project leaders](#project_leaders).
  We'd be happy to point you to some internal documentation to help you out.

Thank you for using CVC4!


Project Leaders
-------------------------------------------------------------------------------

* [Clark Barrett](http://theory.stanford.edu/~barrett/) (Stanford University)
* [Cesare Tinelli](http://homepage.cs.uiowa.edu/~tinelli/) (The University of Iowa)


Authors
-------------------------------------------------------------------------------

For a full list of authors, please refer to the
[AUTHORS](https://github.com/CVC4/CVC4/blob/master/AUTHORS) file.

History
-------------------------------------------------------------------------------

The Cooperating Validity Checker series has a long history.  The Stanford
Validity Checker (SVC) came first in 1996, incorporating theories and its own
SAT solver.  Its successor, the Cooperating Validity Checker (CVC), had a more
optimized internal design, produced proofs, used the Chaff SAT solver, and
featured a number of usability enhancements.  Its name comes from the
cooperative nature of decision procedures in Nelson-Oppen theory combination,
which share amongst each other equalities between shared terms.

CVC Lite, first made available in 2003, was a rewrite of CVC that attempted to
make CVC more flexible (hence the "lite") while extending the feature set: CVC
Lite supported quantifiers where its predecessors did not.

CVC3 was a major overhaul of portions of CVC Lite: it added better decision
procedure implementations, added support for using MiniSat in the core, and had
generally better performance.

CVC4 is the fifth generation of this validity checker line.  It represents a
complete re-evaluation of the core architecture to be both performant and to
serve as a cutting-edge research vehicle for the next several years.  Rather
than taking CVC3 and redesigning problem parts, we've taken a clean-room
approach, starting from scratch.  Before using any designs from CVC3, we have
thoroughly scrutinized, vetted, and updated them.  Many parts of CVC4 bear only
a superficial resemblance, if any, to their correspondent in CVC3.

However, CVC4 is fundamentally similar to CVC3 and many other modern SMT
solvers: it is a DPLL(T) solver, with a SAT solver at its core and a delegation
path to different decision procedure implementations, each in charge of solving
formulas in some background theory.

The re-evaluation and ground-up rewrite was necessitated, we felt, by the
performance characteristics of CVC3.  CVC3 has many useful features, but some
core aspects of the design led to high memory use, and the use of heavyweight
computation (where more nimble engineering approaches could suffice) makes CVC3
a much slower prover than other tools.  As these designs are central to CVC3, a
new version was preferable to a selective re-engineering, which would have
ballooned in short order.
