; REQUIRES: no-competition
; EXPECT: (error "Parse Error: issue-4130.smt2:10.39: expecting bit-width > 0
; EXPECT:
; EXPECT:   (assert (and (= a (bv2nat ((_ int2bv 0) a)))))
; EXPECT:                                        ^
; EXPECT: ")
; EXIT: 1
(set-logic ALL)
(declare-fun a () Int)
(assert (and (= a (bv2nat ((_ int2bv 0) a)))))
(check-sat)
