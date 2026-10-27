; DISABLE-TESTER: dump
; REQUIRES: no-competition
; COMMAND-LINE: --strict-parsing
; EXPECT: (error "Parse Error: strict-parsing-mixed-arith-1.smt2:7.20: Due to strict parsing, we require the arguments of ADD to have the same type")
; EXIT: 1
(set-logic ALL)
(assert (= (+ 1 0.5) 1.5))
(check-sat)
