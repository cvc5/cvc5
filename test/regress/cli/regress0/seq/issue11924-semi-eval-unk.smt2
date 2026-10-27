; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(declare-fun s () (Seq Int))
(assert (exists ((f Int)) (distinct (seq.len (seq.rev s)) (seq.nth (as seq.empty (Seq Int)) (div 0 0)))))
(check-sat)
