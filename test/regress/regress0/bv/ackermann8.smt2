; COMMAND-LINE: --ackermann --no-check-models --no-check-unsat-cores
; EXPECT: unsat
(set-logic QF_UFBV)

(declare-sort S 0)
(declare-sort T 0)

(declare-fun s1 () S)
(declare-fun s2 () S)
(declare-fun s3 () S)

(declare-fun a () (_ BitVec 1))
(declare-fun b () (_ BitVec 1))
(declare-fun c () (_ BitVec 1))

(assert (not (= s1 s2)))
(assert (not (= s2 s3)))
(assert (not (= s3 s1)))

(assert (not (= a b)))
(assert (not (= b c)))
(assert (not (= c a)))

(check-sat)
(exit)

