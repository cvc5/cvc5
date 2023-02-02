This folder contains an example script to execute cvc5 to see if new rewrite
rules are being applied.

## Extensions to the Rewriter

1. `define-cond-rule` which combines a conditional with a rule, with the end goal of removing `cond`.
``` lisp
(define-cond-rule ShlByConst
	((x ?BitVec) (amount Int))
	(< amount (bvwidth x))
	(bvshl x (_ bv amount (bvwidth x)))
	(concat (extract (bvwidth x) (- (bvwidth x) 1 amount_val) x) (bv 0 (bvwidth x))))
(define-cond-rule ShlByConst
	((x ?BitVec) (amount Int))
	(>= amount (bvwidth x))
	(bvshl x (_ bv amount (bvwidth x)))
	(_ bv 0 (bvwidth x)))
```
2. Lifted `extract` operator:
``` lisp
(define-rule ExtractExtract
	((x ?BitVec) (i Int) (j Int) (k Int) (l Int))
	(extract (extract x i j) k l)
	(extract x (+ i j) (- k l)))
```
3. `:list` decoration (implemented)
```lisp
(define-rule ConcatFlatten
	((xs ?BitVec :list)
	 (s ?BitVec)
	 (ys ?BitVec :list)
	 (zs ?BitVec :list))
	(concat xs (concat s ys) zs)
	(concat xs s ys zs))
```

