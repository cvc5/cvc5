; COMMAND-LINE: -i
; EXPECT: sat
(set-logic BV)
(set-info :status sat)
(declare-fun _substvar_16_ () Bool)
(set-option :check-models true)
(declare-fun v2 () Bool)
(push 1)
(assert (exists ((q1 (_ BitVec 12)) (q2 Bool) (q3 (_ BitVec 12))) (xor _substvar_16_ q2 v2)))
(push 1)
(pop 1)
(pop 1)
(assert (forall ((q23 (_ BitVec 6))) v2))
(check-sat)
