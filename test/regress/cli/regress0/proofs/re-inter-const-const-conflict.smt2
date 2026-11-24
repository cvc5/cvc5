; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(assert (not (= (re.inter (str.to_re "a") (str.to_re x) (str.to_re "")) re.none)))
(check-sat)
