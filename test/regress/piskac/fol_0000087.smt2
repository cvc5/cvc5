(set-logic ALL)
(set-info :status unsat)

; forall c_dg:C. forall a_df:A. c_dg + a_df + |UNIVERALSET| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_dg () Int)
(assert (<= c_dg n))
(assert (>= c_dg 0))
(assert (>= (* 2 c_dg) (+ (- n t) 1)))

(declare-fun a_df () Int)
(assert (<= a_df n))
(assert (>= a_df 0))
(assert (>= a_df (- n t)))


(assert (and (< (- (+ (+ c_dg a_df) (set.card UNIVERALSET)) (* 2 n)) 1) (> 1 0)))

(check-sat)
