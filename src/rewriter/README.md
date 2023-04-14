# The Grammar of RARE

This document describe the syntax of the RARE language, which stands for
**r**ewrites, **a**utomatically **re**constructed.

``` dsl
   <rule> ::= (define-rule       <symbol> (<par>*) [<defs>]        <expr> <expr>)
            | (define-rule*      <symbol> (<par>*) [<defs>]        <expr> <expr> [<expr>])
            | (define-cond-rule  <symbol> (<par>*) [<defs>] <expr> <expr> <expr>)
    <par> ::= (<symbol> <sort> [<attr>])
   <sort> ::= ? | <symbol> | ?<symbol> | (<symbol> <sort>+) | (<symbol> <idx>+)
    <idx> ::= ? | <numeral>
   <attr> ::= :list
   <expr> ::= <const> | <id> | (<id> <expr>+)
     <id> ::= <symbol> | (_ <id> <expr>+)
<binding> ::= (<symbol> <expr>)
   <defs> ::= (def <binding>+)
```

## Rules

### Matching

The basic form of a RARE rewrite rule uses `define-rule`. The two expressions in
the body of `define-rule` indicate the *match* and *target* of the rewrites.

``` lisp
(define-rule substr-empty
	((m Int) (n Int))
	(str.substr "" m n)
	"")
```
In this case, the match is `(str.substr "" m n)` and the target is `""`. For example, when the rule is applied to `(str.substr "" 3 5)`, `m,n` are instantiated to `3,5`, respectively, and the expression is rewritten as `""`.

Match is purely syntactic. It matches *syntactically identical* terms. For
example `(= (str.++ x1 x2) x2)`matches `a ++ b = b` but not `a ++ b = c`.


### Conditional Rules

In `define-cond-rule`, an additional expression immediately after the parameter
and definition list restricts the rule to certain cases. The condition has to be
evaluable at the time of rule application.

``` lisp
(define-cond-rule bv-repeat-eliminate-1
	((x ?BitVec) (n Int))
	(> n 1)
	(repeat n x)
	(concat x (repeat (- n 1) x)))
```
This rule is applied on `(repeat 3 ...)` but not `(repeat 1 ...)`.

Implicit assumptions are not required. For example, it is unnecessary in the example below to enforce `0 <= i <= j < (bvsize x)`. The type checker will automatically ensure the expressions entering the reconstruction algorithms have sound types.
``` lisp
(define-rule bv-extract-extract
  ((x ?BitVec) (i Int) (j Int) (k Int) (l Int))
  (extract l k (extract j i x))
  (extract (+ i l) (+ i k) x))
```

### Fixed-Point Rules

The `*` in `define-rule*` indicates that the rule shall be executed by the
reconstruction algorithm until the expression reaches a fixed point. This is an
optimisation and useful for writing rules that iterate over the arguments of
n-ary operators.

Below is an example which recursively flattens a concat using fixed-point rules.
``` lisp
(define-rule* bv-concat-flatten
  ((xs ?BitVec :list)
   (s ?BitVec)
   (ys ?BitVec :list)
   (zs ?BitVec :list))
  (concat xs (concat s ys) zs)
  (concat xs s ys zs))
```
The user can optionally supply a rewrite context to support the continuation. The context indicates how to use the recursion step, which rewrites *match* to *target*, to construct the final result. Below is an example
``` lisp
(define-rule* str-len-concat-rec ((s1 String) (s2 String) (s3 String :list))
	(str.len (str.++ s1 s2 s3))
	(str.len (str.++ s2 s3))
	(+ (str.len s1) _))
```
This rule specifies that the rewrite of `(str.len (str.++ s1 s2 ...))` is the sum of `(str.len s1)` and the result of applying the rule to the term `(str.len (str.++ s2 ...))`

### def construction and variable bindings

The definition list, indicated by `def`, allow the rewrite rule to be more
succinctly expressed and readable. Each variable in the definition list is
replaced by its expression. `def` can be viewed as a special case of `let` which
only exists in the outermost layer.

All used variables in match and target must show up in the parameters list and
`def` list, Variables in the parameter list must be covered by the variables in match. Any unmatched variable will lead to an error.

``` lisp
(define-rule bv-sign-extend-eliminate
	((x ?BitVec) (n Int))
	(def (s (bvsize x)))
	(sign_extend n x)
	(concat (repeat n (extract (- s 1) (- s 1) x)) x))
```

## Adding new operators

The RARE parser is located at `src/rewriter`. To add a new operator,
write a new enumeration entry in `src/rewriter/node.py`. The syntax and
processing are controlled by `rewriter.py` and `parser.py`.

The symbols usable in `(<id> <expr>+)` can be found in `node.py`. The sorts
available can be found in `mkrewrites.py`.

## Changes from Previous Works

In comparison to
[fmcad22](https://ieeexplore.ieee.org/abstract/document/10026573), we have
removed the `let` expression.  `let` is replaced by `def` which allow symbols to
be shared across the condition, source, and target terms.

We also deleted the `const` modifier the rationale is that there are 3 reasons to use `:const`:
1. There should not be a rule that is only sound when its arguments are constant, so `:const` should not exist in this case.
2. The evaluation of operator applications of all constant arguments is handled by the rewriter, and therefore rules evaluating constant expressions should not exist in RARE
3. There are some conditional rules in `theory/bv` which only apply when the
   arguments satisfy a condition. In this case, we could match the required argument using a `(bv v n)` term with variable bit width `n` instead of an abstract bitvector term `(y ?BitVec)`. For example,
``` lisp
(define-cond-rule bv-udiv-pow2-1p
  ((x ?BitVec) (v Int) (n Int))
  (def (power (int.log2 v)))
  (and (int.ispow2 v) (> v 1))
  (bvudiv x (bv v n))
  (concat (bv 0 power) (extract (- n 1) power x)))
```

More information can be found in other works but beware of changes.

### Gradual Types

See `mkrewrites.py` for the supported gradual types. Gradual types mean that the
exact type does not have to be specified in the RARE rule. For example,
`?BitVec` could indicate the bitvector type of an unknown width that will only
be instantiated during rule application.

Example gradual type in `eq`
``` lisp
(define-rule eq-refl ((t ?)) (= t t) true)
```
This matches two semantically equal terms `t` and rewrite the result to `true` regardless of typing.

Gradual types lose information. For example, the information about the width of a bitvector is implicit albeit it can be recovered using `bvsize`. For example:
``` lisp
(define-rule* bv-concat-flatten
  ((xs ?BitVec :list)
   (s ?BitVec)
   (ys ?BitVec :list)
   (zs ?BitVec :list))
  (concat xs (concat s ys) zs)
  (concat xs s ys zs))
```
In this case, the bitvectors in the list `xs`, `ys`, `zs` do not have to have the same bitwidth.
