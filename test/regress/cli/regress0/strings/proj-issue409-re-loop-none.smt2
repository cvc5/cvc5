(set-logic QF_SLIA)
(assert (str.in_re (str.from_code 0) ((_ re.loop 2 1) re.all)))
(set-info :status unsat)
(check-sat)
