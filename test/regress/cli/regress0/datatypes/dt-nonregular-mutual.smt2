; SCRUBBER: grep -o "Cannot handle datatype [A-Z] that is not simply regular"
; EXPECT: Cannot handle datatype P that is not simply regular
; EXIT: 1
(set-logic ALL)
(declare-datatypes ((P 1) (Q 1)) (
  (par (X) ((p0) (p1 (p1a (Q X)))))
  (par (Y) ((q0) (q1 (q1a (Array Int (P (Array Y Y)))))))
))
(declare-const x (P Int))
(check-sat)
