; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(assert (not (= (re.union (str.to_re x) (str.to_re "b") (re.range "a" "c") (str.to_re "z") (re.* (str.to_re "z"))) (re.union (re.range "a" "c") (str.to_re x) (re.* (str.to_re "z"))))))
(check-sat)
