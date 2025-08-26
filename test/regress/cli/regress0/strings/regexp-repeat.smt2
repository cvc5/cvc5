; EXPECT: unsat
(set-logic ALL)

(declare-fun s () String)

(assert (str.in_re s ((_ re.^ 4) (str.to_re "A"))))
(assert (str.in_re s ((_ re.^ 3) (str.to_re "B"))))

(check-sat)
