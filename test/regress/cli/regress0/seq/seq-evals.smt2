; EXPECT: unsat
(set-logic ALL)
(assert (or
(not (= (seq.replace (seq.++ (seq.unit 0) (seq.unit 1) (seq.unit 2)) (seq.++ (seq.unit 1) (seq.unit 2)) (as seq.empty (Seq Int))) (seq.unit 0)))
(not (= (seq.contains (seq.++ (seq.unit 0) (seq.unit 1) (seq.unit 2)) (seq.++ (seq.unit 1) (seq.unit 3))) false))
(not (= (seq.nth (seq.++ (seq.unit 0) (seq.unit 1) (seq.unit 2) (seq.unit 5)) 3) 5))
(not (= (seq.contains (seq.++ (seq.unit (set.singleton 0)) (seq.unit (set.union (set.singleton 2) (set.singleton 1))) (seq.unit (set.singleton 0))) 
                      (seq.unit (set.union (set.singleton 1) (set.singleton 3)))) false))

))
(check-sat)
