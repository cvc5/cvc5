; COMMAND-LINE: -q
; EXPECT: sat
(set-info :smt-lib-version 2.7)
(set-logic ALL)
(declare-sort-parameter foo)
(check-sat)
