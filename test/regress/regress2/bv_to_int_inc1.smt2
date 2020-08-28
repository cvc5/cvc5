; COMMAND-LINE: --incremental --solve-bv-as-int=sum
; EXPECT sat
; EXPECT sat
; EXPECT unsat
; EXPECT sat
(set-logic QF_BV)
(set-option :incremental true)
(declare-fun a () (_ BitVec 3))
(declare-fun b () (_ BitVec 3))
(declare-fun c () (_ BitVec 3))

(assert (bvult a (bvand b c)))
(check-sat)
; EXPECT: sat

(push 1)
(assert (bvult c b))
(check-sat)
; EXPECT: sat


(push 1)
(assert (bvugt c b))
(check-sat)
; EXPECT: unsat
(pop 2)

(check-sat)
; EXPECT: sat
(exit)
