; COMMAND-LINE: --lang=smt2.6
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-datatype Color ( ( red ) ( green ) ( blue ) ))

(declare-fun a () Color)
(declare-fun b () Color)
(declare-fun c () Color)
(declare-fun d () Color)

(assert (or (distinct a b c d)
 (< (match a ((red 5) (green 3) (blue 2))) 0)
 (< (match b ((red 2) (x 1))) 0)
 ))

(check-sat)
