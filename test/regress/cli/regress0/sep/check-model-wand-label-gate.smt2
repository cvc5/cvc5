; COMMAND-LINE: --debug-check-models
; ERROR-SCRUBBER: sed -e 's/__L[A-Za-z0-9_]*/L/g' -e '/^The fact: .*@sep_label/!d'
; EXPECT: sat
; EXPECT-ERROR: The fact: (@sep_label (wand (pto x x) false) L)
; EXPECT-ERROR: The fact: (not (@sep_label (pto x x) L))
;
; Pins the label gate. A magic wand introduces labels for the heaps it
; quantifies over, and their model values can perfectly well overlap the
; locations of the heap the model does describe. Restricting the model heap to
; such a label answers a question about a different heap, so SepModelChecker
; refuses those labels and the fact is reported as unverified.
;
; Without that gate the second fact below is instead "confirmed" against the
; model heap and its warning disappears, which is silent: the benchmarks that
; would notice all carry DISABLE-TESTER: model and nothing asserts anything
; about their output. Hence this test.
;
; The scrubber keeps only the labelled facts and normalises the skolem names,
; which are the volatile part.
(set-logic QF_ALL)
(declare-heap (Int Int))
(declare-fun x () Int)
(assert (wand (pto x x) false))
(check-sat)
