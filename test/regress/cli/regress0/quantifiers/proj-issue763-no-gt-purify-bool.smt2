; COMMAND-LINE: --mbqi
; EXPECT: unknown
; This benchmark is sat, but the only model MBQI finds for the array variable
; is a constant array. Constant arrays cannot be used as instantiations
; unless --arrays-exp is enabled, so MBQI fails to instantiate and the answer
; is unknown. With --arrays-exp, the answer is sat.
; The model tester is disabled since with --debug-check-models, the answer
; is sat.
; DISABLE-TESTER: model
(set-logic ALL)
(declare-const x5 (Seq Bool))
(declare-const x (Array Bool Bool))
(assert (not (select x (exists ((_x (Seq Bool))) (forall ((x (Array Bool Bool))) (select x (seq.prefixof x5 _x)))))))
(check-sat)
