; COMMAND-LINE: --sets-to-bags=relaxed
; SCRUBBER: grep -o "since it has fields of set type"
; EXPECT: since it has fields of set type
; EXIT: 1
(set-logic ALL)
(declare-fun p () (Tuple (Set Int) Int))
(assert (set.member 1 ((_ tuple.select 0) p)))
(check-sat)
