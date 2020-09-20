; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1   --no-check-unsat-cores
; EXPECT: sat
(set-logic ALL)
(declare-fun A () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(assert (distinct (select A x) (select A y)))
(check-sat)
