(set-logic ALL)
(set-info :status unsat)

; forall c_el:C. forall b_ek:B. forall a_ej:A. c_el + b_ek + 2a_ej + |~f| - 4n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_el () Int)
(assert (<= c_el n))
(assert (>= c_el 0))
(assert (>= (* 2 c_el) (+ (- n t) 1)))

(declare-fun b_ek () Int)
(assert (<= b_ek n))
(assert (>= b_ek 0))
(assert (>= (* 2 b_ek) (+ (+ n (* 3 t)) 1)))

(declare-fun a_ej () Int)
(assert (<= a_ej n))
(assert (>= a_ej 0))
(assert (>= a_ej (- n t)))


(assert (and (< (- (+ (+ (+ c_el b_ek) (* 2 a_ej)) (set.card (set.minus UNIVERALSET f))) (* 4 n)) 1) (> 1 0)))

(check-sat)
