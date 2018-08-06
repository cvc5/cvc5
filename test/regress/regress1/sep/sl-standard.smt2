(set-logic QF_ALL)
(set-info :source | CVC4 - Andrew Reynolds |)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)

(declare-heap (Loc Loc))

(declare-const loc0 Loc)

(declare-const u Loc)
(declare-const v Loc)
(declare-const y Loc)
(declare-const y0 Loc)
(declare-const y00 Loc)
(declare-const t Loc)
(declare-const t0 Loc)
(declare-const t00 Loc)

(define-fun pos2 ((x Loc) (a Loc) (i Int)) Bool (or (and (pto x a) (= i 0)) (sep (pto x a) (or (and (pto a y) (= (- i 1) 0)) (sep (pto a y) (or (and (pto y y0) (= (- (- i 1) 1) 0)) (sep (pto y y0) (and (pto y0 y00) (= (- (- (- i 1) 1) 1) 0)))))))))

(define-fun neg2 ((z Loc) (b Loc) (j Int)) Bool (or (and (not (pto z b)) (= j 0)) (sep (pto z b) (or (and (not (pto b t)) (= (- j 1) 0)) (sep (pto b t) (or (and (not (pto t t0)) (= (- (- j 1) 1) 0)) (sep (pto t t0) (and (not (pto t0 t00)) (= (- (- (- j 1) 1) 1) 0)))))))))

;------- f -------
(assert (= t y))
(assert (= t0 y0))
(assert (not (= t00 y00)))
;-----------------

(assert (pos2 u v 3))
(assert (not (neg2 u v 3)))

(check-sat)
