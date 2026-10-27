; EXPECT: unsat
(set-logic ALL)
(assert (exists ((!2 (_ BitVec 32))) (not (= !2 (bvxor !2 (bvxor !2 !2))))))
(check-sat)
