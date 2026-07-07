; EXPECT: unsat
(set-logic ALL)
(declare-const f Int)
(assert (>= f 0))
(assert (not (or (or (or (<= 9 f) (and (distinct 8 f) (and (distinct 7 f) (and (distinct 6 f) (and (distinct 5 f) (and (distinct 4 f) (and (distinct 3 f) (and (distinct 2 f) (and (distinct 1 f) (distinct 0 f)))))))))) (or (distinct (= 8 f) (distinct (= 7 f) (distinct (= 6 f) (distinct (= 5 f) (distinct (= 4 f) (= 3 f)))))) (distinct (= 5 f) (distinct (= 4 f) (distinct (= 3 f) (distinct (= 2 f) (distinct (= 1 f) (= 0 f)))))))) (and (= (= 8 f) (distinct (= 7 f) (= 6 f))) (and (= (= 5 f) (distinct (= 4 f) (= 3 f))) (= (= 2 f) (distinct (= 1 f) (= 0 f))))))))
(check-sat)
