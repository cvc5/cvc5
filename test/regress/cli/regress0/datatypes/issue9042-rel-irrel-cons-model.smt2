; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-datatypes ((C 0)) (((J) (H))))
(declare-datatypes ((R 0) (Q 0)) (((D) (G (s0 Q))) ((E (s1 C) (s2 R) (s3 Int) (s4 R)))))
(declare-datatypes ((B 0)) (((B (s5 Bool)))))
(declare-fun v () Int)
(declare-fun t () R)
(declare-fun n (Int R) R)
(declare-fun N (R) B)
(assert (not ((_ is D) (n v t))))
(assert (not (s5 (N (s2 (s0 (n v t)))))))
(check-sat)
(assert (= (n v t) (G (E H (s2 (s0 D)) (s3 (s0 D)) (s4 (s0 D))))))
(check-sat)
