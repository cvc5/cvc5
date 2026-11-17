; EXPECT: (error "Parse Error: bv-const-non-numeral.smt2:6.23: Expected a numeral in bit-vector constant `bv-1'")
; EXIT: 1
; DISABLE-TESTER: dump
(set-logic ALL)
(declare-const x (_ BitVec 4))
(assert (= x (_ bv-1 4)))
(check-sat)
