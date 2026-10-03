; REQUIRES: unrestricted-mode
; REQUIRES: no-windows
; COMMAND-LINE: --learned-rewrite --check-models
; ERROR-SCRUBBER: sed -e '/^does not hold in the separation logic heap model/!d'
; EXPECT-ERROR: does not hold in the separation logic heap model.
; EXIT: -6
;
; The check firing is an abort, which subprocess reports as -6 on POSIX
; but not on Windows, hence the REQUIRES guard.
;
; A model check that FAILS, on purpose. See
; check-model-detects-unsound-wand.smt2 for the rationale.
;
; (sep p p p) with p = (pto x y) needs the heap to split into three disjoint
; sub-heaps each satisfying (pto x y), i.e. three disjoint singleton heaps all
; at location x, which is impossible. Without --learned-rewrite cvc5 correctly
; answers unsat; with it, sat. Found by Murxla.
;
; check-models catches it by direct evaluation against the heap model; the
; abort is the check firing.
;
; WHEN THE UNDERLYING UNSOUNDNESS IS FIXED, this benchmark becomes ordinary:
; delete the ERROR-SCRUBBER, EXPECT-ERROR and EXIT lines and expect unsat. The
; test failing is the signal that someone fixed it.
(set-logic QF_ALL)
(declare-heap (Int Int))
(declare-const x Int)
(declare-const y Int)
(assert (let ((p (pto x y))) (sep p p p)))
(assert (pto x y))
(check-sat)
