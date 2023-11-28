; SCRUBBER: grep -v -E '.*'
; EXIT: 0
(set-logic ALL)
(set-option :produce-unsat-cores true)
(set-option :sygus-enum smart)
(assert (distinct (= seq.empty seq.empty seq.empty) (set.member seq.empty (set.singleton seq.empty))))
(find-synth :rewrite_input)
