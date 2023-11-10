; SCRUBBER: grep -v -E '.*'
; EXIT: 0
(set-logic ALL)
(declare-const x (Bag Bool))
(assert (> (bag.card (bag.inter_min x bag.empty)) (bag.card (bag.inter_min x bag.empty))))
(find-synth :rewrite_input)
