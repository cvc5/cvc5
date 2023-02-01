This folder contains an example script to execute cvc5 to see if new rewrite
rules are being applied.

## Extensions to the Rewriter

1. ShlByConst
```lisp
(define-rule ShlByConst (
		(amount Int :const)
		(x ?BitVec)
	)
	(let ((l (len x)))
		(cond
			((= amount 0) x)
			((>= amount l) (_ bv 0 l))
			(concat (extract x (- l 1 amount) l)
			        (_ bv 0 amount))
			))
```
2. ConcatFlatten
```lisp
(define-rule ConcatFlatten (
		(?))
	(concat [(concat ...)|...])
	(concat ...))
```
3. Constant evaluation
```lisp
(define-rule BvIteConstCond (
		(c (_ BitVec 1) :const)
		(x (_ BitVec 8))
		(y (_ BitVec 8))
	)
	(bvite c x y)
	(cond
		((= c (_ bv 0 1)) y)
		(x)))
```
4. Operation `bvite` in `smt2` files
5. The `ExtractConcat` rule which requires a loop coupled with conditional on variable sizes. Not sure how this could work.
