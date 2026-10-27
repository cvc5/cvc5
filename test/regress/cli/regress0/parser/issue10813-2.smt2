; DISABLE-TESTER: dump
; SCRUBBER: grep -o 'Negative numerals are forbidden in indices'
; EXPECT: Negative numerals are forbidden in indices
; EXIT: 1
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(assert (= (bvadd x y) (_ bv10 -2)))
(check-sat)
