; COMMAND-LINE: --sets-ext
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () (Set Int))

(assert (= x (set.union (set.singleton 0) (set.singleton 1))))

(assert (not (set.member 0 (as set.universe (Set Int)))))

(check-sat)
