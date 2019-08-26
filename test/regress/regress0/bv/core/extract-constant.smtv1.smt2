(set-option :incremental false)
(meta-info :status unsat)
(set-logic QF_BV)
(check-sat-assuming ( (not (= ((_ extract 6 2) (_ bv56 9)) (_ bv14 5))) ))
