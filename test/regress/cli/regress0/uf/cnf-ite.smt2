; COMMAND-LINE: --simplification=none
; EXPECT: unsat

(set-logic QF_UF)
(set-info :status unsat)
(declare-sort U 0)

(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun d () U)
(declare-fun e () U)
(declare-fun h () U)
(declare-fun i () U)

(assert (or 
(ite (= (f a) d) (not (= d (f b))) (= a c))
(ite (not (= (f a) d)) (= d e) (not (= d (f b))))
(not (ite (not (= (f a) d)) (= d e) (= d (f b))))
(not (ite (= (f a) d) (= d (f b)) (= a c)))
(ite (not (= (f a) e)) (= e (f b)) (= a c))
(ite (= (f a) e) (= e e) (= e (f b)))
(not (ite (= (f a) e) (= e e) (not (= e (f b)))))
(not (ite (not (= (f a) e)) (not (= e (f b))) (= a c)))
(= a b)
))

(assert (and (= (f a) d) (= d (f b))))
(assert (and (not (= (f a) e)) (not (= e (f b)))))

(assert (not (= a b)))

(check-sat)
