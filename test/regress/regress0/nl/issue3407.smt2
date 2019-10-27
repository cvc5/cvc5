; COMMAND-LINE: -q
; EXPECT: sat
(set-logic NRA)
(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= (* a b) 1))
; This problem involves using techniques for repairing model values to satisfy
; non-linear constraints. We use -q to suppress a warning about using
; approximate model values.
(check-sat)
