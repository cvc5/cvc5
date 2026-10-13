; COMMAND-LINE: --rlimit-per=1 --produce-models
; SCRUBBER: sed -e '2,$s/.*/out/'
; EXPECT: unknown
; EXPECT: out
; EXPECT: out
; EXPECT: out
; EXPECT: out
; Model queries after an abort in preprocessing must not crash.
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
(get-model)
(get-value (x))
