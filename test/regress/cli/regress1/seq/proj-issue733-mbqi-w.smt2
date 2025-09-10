; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-option :mbqi-enum true)
(declare-const x (Seq Bool))
(assert (distinct (seq.at x 9510904) (seq.++ (seq.at x 9510904) (seq.rev (seq.at x 9510904)))))
(check-sat)
