; DISABLE-TESTER: dump
; SCRUBBER: grep -o 'Numerals must fit into 32-bit unsigned integers'
; EXPECT: Numerals must fit into 32-bit unsigned integers
; EXIT: 1
(set-logic QF_BV)
(declare-const x (_ BitVec 4294967296))
(check-sat)
