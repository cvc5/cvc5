(set-logic ALL)
(set-info :status unsat)
(assert (str.in_re "" ((_ re.loop 1 0) (str.to_re ""))))
(check-sat)
