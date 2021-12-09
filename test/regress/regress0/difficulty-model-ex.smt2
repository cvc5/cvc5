; COMMAND-LINE: --produce-difficulty --difficulty-mode=model-check
; SCRUBBER: sed 's/.*//g'
; EXIT: 0

(set-logic ALL)
(set-option :produce-difficulty true)
(declare-fun P (Int) Bool)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (= z 78))

(assert (! (= (* x x) z) :named a1))

(assert (= y 0))

(assert (P y))

(check-sat)

(get-difficulty)
