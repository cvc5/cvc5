(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall a_gl:A. forall a_gk:A. C(a_gl & a_gk)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_gl () (Bag Int))

(assert (bag.subbag a_gl UNIVERALSET))
(assert (>= (bag.card a_gl) (- n t)))

(declare-fun a_gk () (Bag Int))

(assert (bag.subbag a_gk UNIVERALSET))
(assert (>= (bag.card a_gk) (- n t)))


(assert (not (>= (* 2 (bag.card (bag.inter_min a_gl a_gk))) (+ (- n t) 1))))

(check-sat)
