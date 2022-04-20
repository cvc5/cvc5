; COMMAND-LINE: --ackermann
; EXPECT: sat
(set-logic QF_UFBV)

(declare-sort S 0)
(declare-sort T 0)

(declare-fun s1 () S)
(declare-fun s2 () S)
(declare-fun t1 () T)
(declare-fun t2 () T)

(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))

(declare-fun f (S) (_ BitVec 4))
(declare-fun g (S) S)
(declare-fun h (T) S)
(declare-fun i (T) T)

(assert (= (f s1) (bvand a b)))
(assert (= (f s2) (bvand a b)))

(assert (= (f (g s1)) (f (h (i t1)))))
(assert (= (f (g (h (i t2)))) (f (h (i t2)))))
(assert (= t1 t2))
(assert (= s1 (h (i t2))))

(check-sat)
(exit)

