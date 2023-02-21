# Rewriter Syntax Extension

Base on the following papers:
1. (Andreas' thesis)

## Removal of const modifier

All constant modifiers `:const` and evaluation backdoors are removed in favour of operator elimination laws.

## Removal of cond

`cond` is removed  in favour of `define-cond-rule`.

## Removal of let

The `let` construct is removed (it was not working either) in favour of the
following syntax. It has the benefit that the rewrite source and target can
share def constructs.

``` lisp
(define-rule ...
	<variables>
	[(def ((x1 t1) ...))]
	<rewrite-source>
	<rewrite-target>
)
```
