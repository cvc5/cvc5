(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

(assert (or

(not (= (str.replace (str.++ x x) "A" "B") (str.replace x "" (str.replace x "A" "B"))))

(not (= (str.replace (str.++ x y "B" x y) "A" z) (str.++ (str.replace (str.++ x y) "A" z) "B" x y)))

))

(check-sat)
