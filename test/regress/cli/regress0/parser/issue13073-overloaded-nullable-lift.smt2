; DISABLE-TESTER: dump
; SCRUBBER: grep -o "Overloaded constants must be type cast."
; EXPECT: Overloaded constants must be type cast.
; EXIT: 1
(set-logic ALL)
(declare-fun f (Int) Int)
(declare-fun f (Bool) Bool)
(declare-const x (Nullable Int))
(assert (= ((_ nullable.lift f) x) x))
(check-sat)
