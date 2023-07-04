; COMMAND-LINE: --tlimit-per=500 --check-models
; SCRUBBER: grep -v -E '.*'
; EXIT: 0
; In this example, a finite grammar is inferred as the set of possible terms in rewrites.
; We terminate with an exception to indicate that the rewrite rule synthesis finished.
(set-logic QF_S)
(declare-fun s () String)
(declare-fun i () String)
(declare-fun x () String)
(assert (or (= x i) (= x s)))
(assert (str.in_re x (re.* (re.++ re.allchar re.allchar))))
(find-synth :rewrite_input)
