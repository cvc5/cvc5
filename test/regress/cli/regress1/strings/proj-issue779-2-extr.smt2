; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(assert (distinct (str.suffixof "A" (str.replace x "A" "")) (str.suffixof "A" (str.replace x "A" (str.replace "B" (str.replace x (str.replace_all (str.replace x "" "") (str.replace x "A" "B") x) "") "A")))))
(check-sat)
