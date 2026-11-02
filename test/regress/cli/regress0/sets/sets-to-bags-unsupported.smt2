; COMMAND-LINE: --sets-to-bags=setof
; SCRUBBER: grep -o "Cannot convert the set operator rel.transpose"
; EXPECT: Cannot convert the set operator rel.transpose
; EXIT: 1
(set-logic ALL)
(declare-fun R () (Relation Int Int))
(assert (set.member (tuple 1 2) (rel.transpose R)))
(check-sat)
