; DISABLE-TESTER: dump
; SCRUBBER: grep -o "symbols starting with . and @ are reserved in SMT-LIB"
; EXPECT: symbols starting with . and @ are reserved in SMT-LIB
; EXIT: 1
(set-logic ALL)
(declare-datatypes ((@ 0)) (((V))))
(check-sat)
