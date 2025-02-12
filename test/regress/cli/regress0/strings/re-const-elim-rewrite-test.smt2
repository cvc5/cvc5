; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)

(assert (or
(not (= (str.in_re x (re.inter (re.* (str.to_re "A")) (str.to_re "AAAA") (re.* (str.to_re "AA")))) (str.in_re x (str.to_re "AAAA"))))
(not (= (str.in_re x (re.inter (re.* (str.to_re "A")) (str.to_re "B") (str.to_re "A"))) (str.in_re x re.none)))
(not (= (str.in_re x (re.union (re.* (str.to_re "A")) (str.to_re "AAA") (str.to_re "A"))) (str.in_re x (re.* (str.to_re "A")))))

))
(check-sat)
