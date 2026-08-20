; REQUIRES: no-windows
; COMMAND-LINE: --check-models
; ERROR-SCRUBBER: sed -e '/^separation logic assertion refuted by subsolver/!d'
; EXPECT-ERROR: separation logic assertion refuted by subsolver with the model heap pinned.
; EXIT: -6
;
; The check firing is an abort, which subprocess reports as -6 on POSIX
; but not on Windows, hence the REQUIRES guard.
;
; A model check that FAILS, on purpose. Every other check-model test here
; asserts the absence of a false alarm; this one asserts that a real one is
; caught, which is the property that actually matters.
;
; cvc5 answers sat for this nested wand and reports a heap that does not
; satisfy the assertion. With H = { a -> c } and w = (wand (wand p p) p) where
; p = (pto a c): w holds on H, because the only heap disjoint from H that
; satisfies (wand p p) is the empty heap and H (+) {} |= p; but (sep w Q) is
; false on H, because a single cell cannot be split so that both w and
; Q = (pto b c) hold. So (= (sep w Q) w) is (= false true) on cvc5's own
; model. Found by Murxla.
;
; check-models catches it by pinning the heap to the model heap and asking a
; subsolver, which refutes the assertion; the abort is the check firing.
;
; WHEN THE UNDERLYING UNSOUNDNESS IS FIXED, this benchmark becomes ordinary:
; delete the ERROR-SCRUBBER, EXPECT-ERROR and EXIT lines and replace them with
; the expected result. The test failing is the signal that someone fixed it.
(set-logic QF_ALL)
(declare-heap (Int Int))
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (let ((p (pto a c)))
          (let ((w (wand (wand p p) p)))
            (= (sep w (pto b c)) w))))
(check-sat)
