; SCRUBBER: grep -o "is not regular"
; EXPECT: is not regular
; EXIT: 1
; DISABLE-TESTER: dump
(set-logic ALL)
(declare-datatypes ((P 1) (Q 1)) (
  (par (X) ((p0) (p1 (p1a (Q X)))))
  (par (Y) ((q0) (q1 (q1a (Array Int (P (Array Y Y)))))))
))
(declare-const x (P Int))
(assert ((_ is p1) x))
(check-sat)
