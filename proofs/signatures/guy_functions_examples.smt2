(set-logic QF_UF)
; (set-option :debug theory-proof-debug)
(set-option :debug equality)
(set-option :debug "equality::internal")
(set-option :debug "equality::graph")
(set-option :debug "equality-proof-debug")
					;(set-option :debug gk-proofs-functionCalls)

(declare-sort s 0)

(declare-fun a1 () s)
(declare-fun b1 () s)
(declare-fun a2 () s)
(declare-fun b2 () s)

(declare-fun f (s s) s)

(assert (= a1 b1))
(assert (= a2 b2))
(assert (not (= (f a1 a2) (f b1 b2))))

(check-sat)
(exit)
