; COMMAND-LINE: --dt-stc-ind --conjecture-gen
; DISABLE-TESTER: unsat-core
; EXPECT: unsat
(set-logic UFDT)
(declare-datatypes ((N 0)) (((s (y N)) (z))))
(declare-fun plus2 (N N) N)
(assert (forall ((a N)) (! (= (plus2 a z) z) :pattern ((plus2 a z)))))
(assert (forall ((a N)) (! (= (plus2 a (s z)) (s z)) :pattern ((plus2 a (s z))))))
(assert (forall ((a N) (b N)) (! (= (plus2 a (s (s b))) (s (s (plus2 a b)))) :pattern ((plus2 a (s (s b)))))))
(declare-fun plus1 (N N) N)
(assert (forall ((a N)) (! (= (plus1 a z) z) :pattern ((plus1 a z)))))
(assert (forall ((a N) (b N)) (! (= (plus1 a (s b)) (s (plus1 a b))) :pattern ((plus1 a (s b))))))
(assert (not (forall ((a N) (b N)) (= (plus1 a b) (plus2 a b)))))
(declare-fun m (N N) N)
(declare-fun q (N N N) N)
(assert (forall ((m N)) (= m (q z z m))))
(assert (exists ((y N)) (= (m z y) (q z z z))))
(check-sat)