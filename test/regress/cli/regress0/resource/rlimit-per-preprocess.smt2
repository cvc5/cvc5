; COMMAND-LINE: --rlimit-per=1
; EXPECT: unknown
; EXPECT: (:reason-unknown resourceout)
; The resource limit is reached in preprocessing, which must be aborted.
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
(get-info :reason-unknown)
