; REQUIRES: no-windows
; COMMAND-LINE: --check-models
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
; The last two assertions on their own are unsat: the heap has to be exactly
; the two cells 1 -> 1 and 2 -> 2, while (or sep.emp (pto 3 3)) needs it to be
; empty or a single cell. The first assertion is valid -- sep.emp and
; (pto 1 1) cannot hold of the same heap, so their conjunction is unsat and
; its negation holds of every heap -- so adding it cannot make an unsat
; problem sat. cvc5 answers sat, reporting the heap (sep (pto 2 2) (pto 1 1)).
; Found by random testing.
;
; Unlike its two siblings this needs nothing to provoke it: default options, no
; magic wand, and the refutation is by direct evaluation rather than by the
; subsolver. Under --debug-check-models cvc5 also reports sep.emp as an
; asserted fact the model does not satisfy, labelled with a three-element set,
; and --sep-pre-skolem-emp gives the correct unsat -- which together place the
; fault in the reduction of emp rather than in the model construction.
;
; WHEN THE UNDERLYING UNSOUNDNESS IS FIXED, this benchmark becomes ordinary:
; delete the ERROR-SCRUBBER, EXPECT-ERROR and EXIT lines and expect unsat. The
; test failing is the signal that someone fixed it.
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (not (and sep.emp (pto 1 1))))
(assert (or sep.emp (pto 3 3)))
(assert (sep (pto 1 1) (pto 2 2)))
(check-sat)
