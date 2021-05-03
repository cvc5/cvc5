; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
(set-logic UFDTSLIA)
(set-info :smt-lib-version 2.6)

(declare-datatype Response ((Response$Response (Response$Response$success Bool))))

(push 1)
(declare-fun $BLout$3248$0$1$() Response)
(assert (= $BLout$3248$0$1$ (Response$Response true)))
(check-sat)
(pop 1)

(push 1)
(declare-fun $BLout$3248$2$1$() Response)
(assert (= $BLout$3248$2$1$ (Response$Response true)))
(check-sat)
