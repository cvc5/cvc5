; EXPECT: unsat
(set-logic ALL)
(declare-datatype FList ((cons (head (Set (_ FloatingPoint 4 5))) (tail FList)) (nil)))
(assert false)
(declare-const a FList)
(declare-const b FList)
(assert (= a b))
(check-sat)
