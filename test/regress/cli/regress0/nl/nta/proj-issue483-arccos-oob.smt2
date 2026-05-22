; COMMAND-LINE: --sat-solver=minisat -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(assert (>= real.pi (arccos real.pi)))
(check-sat)
