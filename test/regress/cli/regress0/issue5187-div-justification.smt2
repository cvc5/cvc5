; COMMAND-LINE: --strings-exp -i
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
(set-logic QF_AUFNIA)
(declare-fun _substvar_77_ () Int)
(declare-fun _substvar_82_ () Int)
(declare-const v11 Bool)
(declare-const arr (Array Bool Int))
(push 1)
(declare-const i3 Int)
(declare-const i5 Int)
(assert (= (* 469 _substvar_77_) (div 174 (div 81 81))))
(push 1)
(assert (< 0 (* i5 i3 469 (select (store arr true 81) v11) (+ _substvar_82_ 174 81))))
(push 1)
(push 1)
(check-sat)
(pop 1)
(pop 1)
(push 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(pop 1)
(check-sat)
(pop 1)
(pop 1)
(check-sat)
