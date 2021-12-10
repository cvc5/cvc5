; COMMAND-LINE: --produce-difficulty
; SCRUBBER: sed 's/.*//g'
; EXIT: 0

(set-logic ALL)
(set-option :produce-difficulty true)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)

(assert (or (> a 0) (> b 0) (> c 0)))

(assert (< (ite (> a b) a b) 0))

(check-sat)
(get-difficulty)
