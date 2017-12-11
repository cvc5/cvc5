; COMMAND-LINE: --sets-ext
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () (Set Int))

(assert (= x (union (singleton 0) (singleton 1))))

(assert (not (member 0 (as univset (Set Int)))))

(check-sat)
