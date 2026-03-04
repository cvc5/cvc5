; COMMAND-LINE: --solve-int-as-bv=1
; SCRUBBER: grep -o "Cannot translate to BV"
; EXPECT: Cannot translate to BV
; EXIT: 1
(set-logic ALL)
(declare-const y (_ BitVec 4))
(declare-const t (_ BitVec 8))
(assert (= (bvor t (_ bv3 8)) (bvmul t (_ bv157 8) ((_ zero_extend 4) y) ((_ zero_extend 4) y))))
(check-sat)
