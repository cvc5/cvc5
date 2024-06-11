; DISABLE-TESTER: dump
; SCRUBBER: grep -o '(error "Parse Error: issue9675.smt2:6.46: Invalid argument'
; EXPECT: (error "Parse Error: issue9675.smt2:6.46: Invalid argument
; EXIT: 1
(set-logic ALL)
(assert (= (fp (_ bv0 1) (_ bv0 1) (_ bv0 11))))
