; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Cannot use variable shadowing"
; EXPECT: Cannot use variable shadowing
; EXIT: 1
(set-logic ALL)
(assert (exists ((x Real))
          (let ((?y x))
          (and (<= 0 x) (exists ((x Real)) (forall ((v Real)) (> 0 ?y)))))))
(check-sat)
