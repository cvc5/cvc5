; COMMAND-LINE: --sygus-rr-synth-input
; SCRUBBER: grep -v -E '\(define-fun'
; EXPECT: unknown
(set-logic QF_S)
(declare-fun s () String)
(declare-fun i () String)
(declare-fun x () String)
(assert (or (= x i) (= x s)))
(assert (str.in_re x (re.* (re.++ re.allchar re.allchar))))
(check-sat)
