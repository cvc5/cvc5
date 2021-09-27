; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-sort U 0)
(declare-fun x () U)
(declare-fun y () U)
(check-sat-assuming ( (not (= x y)) ))
(assert (= x y))
(check-sat-assuming ( (not (= x y)) ))
(declare-fun z () U)
(push 1)
(check-sat-assuming ( (not (= x y)) ))
(check-sat-assuming ( (not (= x z)) ))
(check-sat-assuming ( (not (= z x)) ))
(check-sat-assuming ( (= z x) ))
(pop 1)
(check-sat-assuming ( (= z x) ))
