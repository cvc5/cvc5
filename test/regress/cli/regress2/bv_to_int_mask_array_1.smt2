; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1
; COMMAND-LINE: --solve-bv-as-int=bitwise --bvand-integer-granularity=1
; COMMAND-LINE: --solve-bv-as-int=iand --iand-mode=value
; COMMAND-LINE: --solve-bv-as-int=iand --iand-mode=sum
; COMMAND-LINE: --solve-bv-as-int=bv
; EXPECT: unsat
(set-logic ALL)
(declare-fun A () (Array Int Int))
(declare-fun f ((_ BitVec 3)) Int)
(declare-fun x () (_ BitVec 3))
(declare-fun y () (_ BitVec 3))
(assert (distinct (select A (f (bvand x y))) (select A (f (bvor x y)))))
(assert (= x y))
(check-sat)
