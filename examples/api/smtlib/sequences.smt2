(set-logic QF_SLIA)
(set-option :produce-models true)

; create integer sequence constants
(declare-const x (Seq Int))
(declare-const y (Seq Int))

; |x.y.empty| > 1
(assert (> (seq.len (seq.++ x y (as seq.empty (Seq Int)))) 1))
; x = seq(1)
(assert (= x (seq.unit 1)))

(check-sat)
(get-value (x y))
