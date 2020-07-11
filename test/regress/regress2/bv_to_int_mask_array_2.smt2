; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1 --no-check-models  --no-check-unsat-cores --no-check-proofs 
; EXPECT: sat
(set-logic ALL)
(declare-fun A () (Array Int Int))
(declare-fun f ((_ BitVec 3)) Int)
(declare-fun x () (_ BitVec 3))
(declare-fun y () (_ BitVec 3))
(assert (distinct (select A (f (bvand x y))) (select A (f (bvor x y)))))
(check-sat)
