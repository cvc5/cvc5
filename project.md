# SMT Solver Lab

In this project, we are implementing simple theory solvers for integer
difference logic (IDL) in cvc5. cvc5 is a state-of-the-art SMT solver and the
goal of this lab is to give a taste of what it takes to implement new theories
in an SMT solver. The individual steps of this lab build on each other, so it
is advisable to follow them in order.

## Getting the Source Code and Compiling cvc5

Use [Git](https://git-scm.com/) to clone this repository.

```
git clone git@github.com:cvc5/cvc5.git
cd cvc5
```

Then check out the branch that corresponds to this project.

```
git checkout idl-lab
```

Before we get started, we have to compile cvc5. cvc5 can currently be compiled
on Linux and macOS. It can be cross-compiled for Windows but compilation on
Windows itself is not supported at this time. If you are using Windows,
consider using the [Windows Subsystem for Linux
(WSL)](https://docs.microsoft.com/en-us/windows/wsl/install-win10) or a Linux
VM. Depending on your machine, the initial compilation may take a while.

### Method 1: Direct Compilation

Before compiling cvc5, install the required dependencies as listed in
[INSTALL.md](INSTALL.md).

Afterwards, we can configure cvc5 and build it as follows:

```
./configure.sh debug --auto-download --static
cd build
make -j<number of processes>
```

Configuring cvc5 additionally with `--ubsan` and `--asan` enables the undefined
behavior UndefinedBehaviorSanitizer (UBSan) and the AddressSanitizer (ASan).
The former detects [undefined behavior](https://en.wikipedia.org/wiki/Undefined_behavior)
whereas the latter detects memory errors. Compiling the code with UBSan and
ASan incurs a performance penalty but when developping C++ code, it can help
uncover subtle problems and can help with debugging efforts.

### Method 2: Via Nix

[Nix](https://nixos.org/download) is a package manager and environment for
ensuring reproducible builds. Download and install Nix. Then create the file `~/.config/nix/nix.conf` and put in the line
```text
experimental-features = nix-command flakes
```
Executing `nix develop` in the project root drops the current shell into an
environment with all dependencies installed. We can then compile cvc5 with
```
./configure.sh debug --auto-download --static
cd build
make -j<number of processes>
```
Alternatively, `nix build` directly produces a cvc5 executable in `result/`.


## A Simple IDL Solver

In this part of the lab, you will implement a simple IDL solver that supports
model generation (i.e., produces values that satisfy the constraints for
satisfiable instances). Implementing the IDL solver consists of two steps: the
decision procedure and model generation.

### The Decision Procedure

The theory solver takes a set of theory literals of the form `(<= (- y x) n)`
(when the SAT solver decided the theory literal to be `true`) and `(not (<= (-
y x) n))` (when the SAT solver decided the theory literal to be `false`). Note
that the negated literals can be recast to be in the same form as the positive
ones. For the purpose of this lab, we are only considering cases where all the
theory literals have a value assigned (in cvc5, that's when a check is done at
"full effort"). The purpose of the theory solver is to decide whether a given
assignment to theory literals results in a conflict or not.

After compiling cvc5 as described in the previous section, you can try running
it on
[test/regress/cli/regress0/idl/example-rewritten.smt2](test/regress/cli/regress0/idl/example-rewritten.smt2):

```
$ bin/cvc5 --arith-idl-ext ../test/regress/cli/regress0/idl/example-rewritten.smt2
...
Expected result unsat but got sat
...
```

For this project, the example file is part of the _regression tests_. The
regression tests are a collection of tests that are run frequently (e.g., as
part of the CI) to ensure that we do not introduce bugs. Regression tests can
also be run using `ctest`: `ctest -R idl/example-rewritten.smt2`. See [the
documentation](test/regress/README.md) of our regression tests for more
information.

The option `--arith-idl-ext` tells cvc5 that we want to use the IDL solver
instead of the generic arithmetic solver. The error appears because the meta
information for the file says that the result should be `unsat` (`(set-info
:status unsat)`) but cvc5 computed that the result should be `sat`. We have to
implement a decision procedure to detect conflicts to fix this.

For IDL, a decision procedure can be implemented as follows: Given a set of
literals of the form `(<= (- y x) n)`, we can construct a graph where we have
one node for every integer constant and an edge with weight `n` from the node
corresponding to `x` to the node corresponding to `y`. Now, the assignment has
a conflict if and only if the graph contains a negative cycle.

**Task**: The skeleton code in
[src/theory/arith/idl/idl_extension.cpp](src/theory/arith/idl/idl_extension.cpp)
constructs a graph and stores it in `d_matrix`. Your task is to complete
`IdlExtension::negativeCycle()` that returns `true` if the graph contains a
negative cycle and `false` otherwise.

After completing the previous task and making sure that cvc5 now solves
[test/regress/cli/regress0/idl/example-rewritten.smt2](test/regress/cli/regress0/idl/example-rewritten.smt2)
and
[test/regress/cli/regress0/idl/example-rewritten-sat.smt2](test/regress/cli/regress0/idl/example-rewritten-sat.smt2),
try running it on
[test/regress/cli/regress0/idl/example.smt2](test/regress/cli/regress0/idl/example.smt2).
An assertion fails:

```
$ bin/cvc5 --arith-idl-ext ../test/regress/cli/regress0/idl/example.smt2
...
  atom.getKind() == Kind::LEQ
...
```

Compare the assertions in
[test/regress/cli/regress0/idl/example.smt2](test/regress/cli/regress0/idl/example.smt2)
and
[test/regress/cli/regress0/idl/example-rewritten.smt2](test/regress/cli/regress0/idl/example-rewritten.smt2).
The assertions are equivalent but in the latter, all the assertions are of the
form `(<= (- y x) n)`. The SMT-LIB logic
[QF\_IDL](http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_IDL) (quantifier-free
IDL problems) allows constraints of the form `(op (- y x) n)`, `(op (- y x) (-
n))`, and `(op y x)` where `op` is one of `<`, `<=`, `>`, `>=`, `=`, or
`distinct` and not only `(<= (- y x) n)`. Additionally, the constant value `n`
may be on the right-hand or left-hand side. To support the full range of
constraints, we can rewrite them to the latter form in the solver.

**Task**: Complete all `TODO`s in `IdlExtension::ppRewrite()` to rewrite the
IDL constraints to the form that `IdlExtension::processAssertion()` expects.
Test your code by creating SMT-LIB benchmarks that exercise all the different
cases.

_Hint_: Compare the constraints in `test/regress/cli/regress0/idl/example.smt2` and
`test/regress/cli/regress0/idl/example-rewritten.smt2` to get an idea of what the
rewrites should look like. This example only covers parts of the `TODO`s.

If you would like to test your solver with additional inputs, you can use the
[SMT-LIB benchmarks for
QF_IDL](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_IDL).

### Model Generation

If you run cvc5 on
[test/regress/cli/regress0/idl/example-rewritten-sat.smt2](test/regress/cli/regress0/idl/example-rewritten-sat.smt2),
you may have noticed that cvc5 reports a model but the model is wrong (all the
values are zero):

```
$ bin/cvc5 --arith-idl-ext ../test/regress/cli/regress0/idl/example-rewritten-sat.smt2
sat
(model
(define-fun x () Int 0)
(define-fun y () Int 0)
(define-fun z () Int 0)
(define-fun w () Int 0)
)
```

For IDL, a model can be generated by running a single-source shortest paths
algorithm. Conceptually, we add a node to our graph that has edges with weight
0 to all the other nodes and then compute the shortest path from that node to
all the other nodes. The distance of a node becomes its value in the model.

**Task**: Your task for this part of the lab is to complete
`IdlExtension::collectModelInfo()` by computing the values in the `distance`
vector. The skeleton takes those `distance` values and asserts that the values
of the variables are the same as their distance.
