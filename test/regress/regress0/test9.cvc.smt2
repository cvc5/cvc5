; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun P () Bool)
(declare-fun Q () Bool)
(assert (or P Q))
(check-sat-assuming ( (not (or P Q)) ))
