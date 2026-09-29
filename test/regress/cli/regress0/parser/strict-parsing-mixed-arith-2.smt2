; DISABLE-TESTER: dump
; REQUIRES: no-competition
; COMMAND-LINE: --strict-parsing
; EXPECT: (error "Parse Error: strict-parsing-mixed-arith-2.smt2:7.24: Due to strict parsing, we require the arguments of TO_REAL to have type Int")
; EXIT: 1
(set-logic ALL)
(assert (= (to_real 0.0) 0.0))
(check-sat)
