(set-logic ALL)
(set-info :status unsat)
(assert (distinct false (exists ((v String)) (distinct true (str.< (str.replace_all v v "") (str.replace (str.++ v "fi") "fi" "if"))))))
(check-sat)
