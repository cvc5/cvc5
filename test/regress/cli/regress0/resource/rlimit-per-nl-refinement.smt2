; COMMAND-LINE: --incremental --rlimit-per=4000
; EXPECT: unknown
; EXPECT: (:reason-unknown resourceout)
; EXPECT: sat
; The resource limit is reached in the model-based refinement of the
; non-linear extension. This is aborted by an exception caught there. The
; solver remains usable after popping.
(set-logic QF_NRA)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(declare-fun x7 () Real)
(declare-fun x8 () Real)
(declare-fun x9 () Real)
(declare-fun x10 () Real)
(declare-fun x11 () Real)
(push 1)
(assert (> (+ (* x0 x0) (* x0 x1) (* x0 x2) (* x0 x3) (* x0 x4) (* x0 x5) (* x0 x6) (* x0 x7) (* x0 x8) (* x0 x9) (* x0 x10) (* x0 x11) (* x1 x1) (* x1 x2) (* x1 x3) (* x1 x4) (* x1 x5) (* x1 x6) (* x1 x7) (* x1 x8) (* x1 x9) (* x1 x10) (* x1 x11) (* x2 x2) (* x2 x3) (* x2 x4) (* x2 x5) (* x2 x6) (* x2 x7) (* x2 x8) (* x2 x9) (* x2 x10) (* x2 x11) (* x3 x3) (* x3 x4) (* x3 x5) (* x3 x6) (* x3 x7) (* x3 x8) (* x3 x9) (* x3 x10) (* x3 x11) (* x4 x4) (* x4 x5) (* x4 x6) (* x4 x7) (* x4 x8) (* x4 x9) (* x4 x10) (* x4 x11) (* x5 x5) (* x5 x6) (* x5 x7) (* x5 x8) (* x5 x9) (* x5 x10) (* x5 x11) (* x6 x6) (* x6 x7) (* x6 x8) (* x6 x9) (* x6 x10) (* x6 x11) (* x7 x7) (* x7 x8) (* x7 x9) (* x7 x10) (* x7 x11) (* x8 x8) (* x8 x9) (* x8 x10) (* x8 x11) (* x9 x9) (* x9 x10) (* x9 x11) (* x10 x10) (* x10 x11) (* x11 x11)) 100))
(assert (< (+ (* x0 x1 x2) (* x1 x2 x3) (* x2 x3 x4) (* x3 x4 x5) (* x4 x5 x6) (* x5 x6 x7) (* x6 x7 x8) (* x7 x8 x9) (* x8 x9 x10) (* x9 x10 x11) (* x10 x11 x0) (* x11 x0 x1)) 50))
(check-sat)
(get-info :reason-unknown)
(pop 1)
(push 1)
(assert (> x0 1.0))
(check-sat)
(pop 1)
