(set-logic ALL)

(set-info :status sat)

; forall c_dw:C. forall c_dv:C. nonempty(c_dw & c_dv)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_dw () (Set Int))

(assert (set.subset c_dw UNIVERALSET))
(assert (>= (* 2 (set.card c_dw)) (+ (- n t) 1)))

(declare-fun c_dv () (Set Int))

(assert (set.subset c_dv UNIVERALSET))
(assert (>= (* 2 (set.card c_dv)) (+ (- n t) 1)))


(assert (= (set.card (set.inter c_dw c_dv)) 0))

(check-sat)
