# The Grammar of RARE

## Overview

This document describe the syntax of the RARE language, which stands for
**r**ewrites, **a**utomatically **re**constructed.

``` dsl
   <rule> ::= (define-rule       <symbol> (<par>*) [<defs>]        <expr> <expr>)
            | (define-rule*      <symbol> (<par>*) [<defs>]        <expr> <expr> [<expr>])
            | (define-cond-rule  <symbol> (<par>*) [<defs>] <expr> <expr> <expr>)
            | (define-cond-rule* <symbol> (<par>*) [<defs>] <expr> <expr> <expr> [<expr>])
    <par> ::= (<symbol> <sort> [<attr>])
   <sort> ::= ? | <symbol> | ?<symbol> | (<symbol> <sort>+) | (<symbol> <idx>+)
    <idx> ::= ? | <numeral>
   <attr> ::= :list
   <expr> ::= <const> | <id> | (<id> <expr>+)
     <id> ::= <symbol> | (_ <id> <expr>+)
<binding> ::= (<symbol> <expr>)
   <defs> ::= (def <binding>+)
```
The basic form of a RARE rewrite rule uses `define-rule`. The two
expressions in the body of `define-rule` indicate the *match* and *target*
of the rewrites.

``` lisp
(define-rule substr-empty
	((m Int) (n Int))
	(str.substr "" m n)
	"")
```
In this case, the match is `(str.substr "" m n)` and the target is `""`. For example, when the rule is applied to
`(str.substr "" 3 5)`, `m,n` are instantiated to `3,5`, respectively, and the expression is rewritten as `""`.

The `*` in `define-rule*` indicates that the rule shall be executed until it can
no longer apply. In this case the user can supply a rewrite context to support
the continuation.

``` lisp
(define-rule* str-len-concat-rec ((s1 String) (s2 String) (s3 String :list))
	(str.len (str.++ s1 s2 s3))
	(str.len (str.++ s2 s3))
	(+ (str.len s1) _))
```

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

The definition list, indicated by `def`, allow the rewrite rule to be more
succinctly expressed and readable. Each variable in the definition list is
replaced by its expression.

``` lisp
(define-rule bv-sign-extend-eliminate
	((x ?BitVec) (n Int))
	(def (s (bvsize x)))
	(sign_extend n x)
	(concat (repeat n (extract (- s 1) (- s 1) x)) x))
```

## CVC5 Implementation Details

The RARE parser is located at `src/rewriter`. To add a new operator,
write a new enumeration entry in `src/rewriter/node.py`. The syntax and
processing are controlled by `rewriter.py` and `parser.py`.

The symbols usable in `(<id> <expr>+)` can be found in `node.py`. The sorts
available can be found in `mkrewrites.py`.

## Changes from Previous Works

In comparison to [fmcad22], we have removed the `let` and `cond` expressions in
favour of more atomic rewrite rules. `let` is replaced by `<defs>` which allow
symbols to be shared across the condition, source, and target terms.

We also deleted the `const` modifier since the evaluation of constant
expressions should be handled elsewhere.

### Gradual Types

See `mkrewrites.py` for the supported gradual types. Gradual types mean that the
exact type does not have to be specified in the RARE rule. For example,
`?BitVec` could indicate the bitvector type of an unknown width that will only
be instantiated during rule application.

