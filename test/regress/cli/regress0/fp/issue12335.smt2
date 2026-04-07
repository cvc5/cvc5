; EXPECT: sat
(set-logic FP)
(declare-const x Float32)
(declare-const a Float32)
(assert (forall ((V Float32) (A Float32)) (or (not (fp.lt V x)) (not (fp.eq a a)) (not (fp.gt A (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)))) (not (fp.eq (fp.div RNE A V) (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)))))))
(assert (fp.geq a (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))))
(check-sat)
