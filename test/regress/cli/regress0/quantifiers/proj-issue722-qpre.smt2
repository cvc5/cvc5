; EXPECT: unsat
(set-logic ALL)
(set-option :prenex-quant norm)
(declare-const x Bool)
(assert (not (or x (forall ((_x (Array Int Bool))) (or (not x) (not (select _x 0)))))))
(assert (exists ((_x (Array Int Bool))) (select _x 0)))
(check-sat)
