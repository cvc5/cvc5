(set-logic ALL)
(set-info :status unsat)

; forall a_ev:A. a_ev + |~f| - n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_ev () Int)
(assert (<= a_ev n))
(assert (>= a_ev 0))
(assert (>= a_ev (- n t)))


(assert (and (< (* 2 (- (+ a_ev (set.card (set.minus UNIVERALSET f))) n)) (+ (- n t) 1)) (> (+ (- n t) 1) (* 2 0))))

(check-sat)
