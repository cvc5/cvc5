; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(assert (not (= (re.inter (str.to_re "b") (re.range "a" "c") (str.to_re y) (re.* re.allchar) (str.to_re x)) (re.inter (str.to_re "b") (str.to_re x) (str.to_re y)))))
(check-sat)
