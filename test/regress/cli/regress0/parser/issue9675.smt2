; DISABLE-TESTER: dump
; SCRUBBER: grep -o '(error "Parse Error: issue9675.smt2:6.46: invalid argument'
; EXPECT: (error "Parse Error: issue9675.smt2:6.46: invalid argument
; EXIT: 1
(set-logic ALL)
(assert (= (fp (_ bv0 1) (_ bv0 1) (_ bv0 11))))
