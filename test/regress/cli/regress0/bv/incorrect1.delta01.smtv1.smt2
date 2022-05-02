(set-option :incremental false)
(set-info :status sat)
(set-logic QF_BV)
(check-sat-assuming ( (bvult (bvsmod (_ bv0 9) ((_ sign_extend 4) (_ bv29 5))) (_ bv1 9)) ))
