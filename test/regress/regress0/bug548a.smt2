; COMMAND-LINE: --tlimit 1000
; EXPECT: unknown
(set-logic AUFLIA)
(declare-fun f (Int) Int)


; instantiated version : cvc4 answers sat
;(assert (= (f 1) (div 1 10)))
;(assert (= (f 11) (div 11 10)))

; cvc4 answers unsat, should be "sat", cvc4 expected to timeout or answer "unknown"
(assert (forall ((x Int)) (= (f x) (div x 10))))

(assert (= (f 1) 0))
(assert (= (f 11) 1))

(check-sat)
