; COMMAND-LINE: --incremental --rewrite-rules

(set-logic AUFLIA)

(declare-fun R (Int Int) Bool)

;; reflexive
(assert-rewrite ((x Int)) () () (R x x) true)

;; anti-symmetric
(assert-reduction ((x Int) (y Int)) () () ((R x y) (R y x)) (= x y))

;; transitive
(assert-propagation ((x Int) (y Int) (z Int)) () () ((R x y) (R y z)) (R x z))


(declare-fun e1 () Int)
(declare-fun e2 () Int)
(declare-fun e3 () Int)
(declare-fun e4 () Int)

; EXPECT: unsat
(push);;unsat
(assert (not (=> (and (R e1 e2) (R e2 e4) (R e1 e3) (R e3 e4) (= e1 e4)) (= e2 e3))))
(check-sat)
(pop)

; EXPECT: unsat
(push);;unsat
(assert (not (=> (and (R e1 e2) (R e1 e3) (or (R e2 e4) (R e3 e4)) ) (R e1 e4))))
(check-sat)
(pop)

; EXPECT: sat
(push);;sat
(assert (and (not (R e1 e3)) (R e4 e1)))
(check-sat)
(pop)


(exit)
