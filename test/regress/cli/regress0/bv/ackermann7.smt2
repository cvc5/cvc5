; COMMAND-LINE: --ackermann
; EXPECT: sat
(set-logic QF_UFBV)

(declare-sort S 0)
(declare-sort T 0)

(declare-fun s1 () S)
(declare-fun s2 () S)
(declare-fun s3 () S)

(declare-fun t1 () T)
(declare-fun t2 () T)
(declare-fun t3 () T)

(assert (not (= s1 s2)))
(assert (not (= s2 s3)))
(assert (not (= s3 s1)))

(assert (not (= t1 t2)))
(assert (not (= t2 t3)))
(assert (not (= t3 t1)))

(check-sat)
(exit)

