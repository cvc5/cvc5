; COMMAND-LINE: -q
; SCRUBBER: grep -v -E '.*'
; EXIT: 0
(set-logic ALL)
(assert (let ((_let0 (exists ((x Bool)) false))) (distinct _let0 _let0)))
(find-synth :rewrite_input)
