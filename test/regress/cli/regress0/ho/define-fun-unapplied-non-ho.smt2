; REQUIRES: no-competition
; REQUIRES: unrestricted-mode
; EXIT: 1
; SCRUBBER: grep -o "Function terms are only supported with higher-order logic"
; EXPECT: Function terms are only supported with higher-order logic
(set-logic ALL)
(declare-const S (Set Int))
(declare-const T (Set Int))
(define-fun f ((x Int)) Int (+ x 1))
(assert (= S (set.singleton 0)))
(assert (= (set.map f S) T))
(assert (not (set.member 1 T)))
(check-sat)
