(set-logic ALL)
(declare-fun a () String)
(assert (> (str.indexof a "" (* 2 (str.len a))) 0))
(check-sat)
