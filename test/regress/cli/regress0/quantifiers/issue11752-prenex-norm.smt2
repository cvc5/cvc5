; COMMAND-LINE: --prenex-quant=norm -q
; EXPECT: sat
(set-logic ALL)
(declare-const x Bool)
(assert (forall ((v (_ BitVec 1))) (and x (or (exists ((v (_ BitVec 2))) (bvsgt (_ bv1 4) ((_ zero_extend 2) v)))))))
(check-sat)
