; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "expecting bit-width > 0"
; EXPECT: expecting bit-width > 0
; EXIT: 1
(set-logic ALL)
(declare-fun a () Int)
(assert (and (= a (ubv_to_int ((_ int_to_bv 0) a)))))
(check-sat)
