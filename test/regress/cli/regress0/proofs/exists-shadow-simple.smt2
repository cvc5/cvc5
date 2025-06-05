; EXPECT: unsat
(set-logic ADTLIRA)
(assert (exists ((k Int) (k Int)) false))
(check-sat)
