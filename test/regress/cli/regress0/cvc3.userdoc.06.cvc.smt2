; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 12))
(declare-fun t () (_ BitVec 12))
(assert (= x #b11111111))
(assert (= z #b111111110000))
(check-sat-assuming ( (not (= z (concat x #b0000))) ))
(check-sat-assuming ( (not (= ((_ extract 7 0) (concat #b0000 ((_ extract 11 4) z))) x)) ))
