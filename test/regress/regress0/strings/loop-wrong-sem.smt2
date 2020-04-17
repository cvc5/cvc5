(set-logic ALL)
(set-info :status unsat)
(assert (str.in.re "" ((_ re.loop 1 0) (str.to.re ""))))
(check-sat)
