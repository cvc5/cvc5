; EXPECT: unsat
(set-logic ALL)
(declare-fun s () String)

(assert (str.in_re s 
      (re.inter (re.inter (re.union (str.to_re "A") (str.to_re "B")) (re.union (str.to_re "C") (str.to_re "D")))
                             (re.comp (re.union (str.to_re "A") (str.to_re "B"))))))
(check-sat)
