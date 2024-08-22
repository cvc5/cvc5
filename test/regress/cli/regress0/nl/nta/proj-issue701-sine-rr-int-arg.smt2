; EXPECT: unsat
(set-logic ALL)
(check-sat-assuming ((<= 0.0 (sin (+ 1.0 real.pi)))))
