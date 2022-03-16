; COMMAND-LINE: --solve-int-as-bv=3
; SCRUBBER: sed -n "s/.*\(Not enough bits\).*: 4.*/\1/p"
; EXPECT: Not enough bits
; EXIT: 1
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
; The negative constant fits, the positive does not
(assert (= (- 4) (* x y)))
(assert (= 4 (* x y)))
(check-sat)
