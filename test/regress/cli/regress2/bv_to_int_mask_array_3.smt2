; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1
; COMMAND-LINE: --solve-bv-as-int=bitwise --bvand-integer-granularity=1
; EXPECT: sat
(set-logic ALL)
(declare-fun A () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(assert (distinct (select A x) (select A y)))
(check-sat)
