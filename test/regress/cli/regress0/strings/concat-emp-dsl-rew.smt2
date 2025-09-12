; EXPECT: unsat
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(assert (not
(= (str.in_re (str.++ s t) (str.to_re "")) (and (= s "") (= t "")))
))
(check-sat)
