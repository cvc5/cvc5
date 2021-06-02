; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic QF_UF)
(set-option :produce-proofs true)
(set-option :incremental true)
(declare-fun p () Bool)
(declare-fun q () Bool)

(push)
(assert (not (= p (not q))))
(assert p)
(check-sat)
(pop)

(push)
(assert (not (= (not q) p)))
(assert p)
(check-sat)
(pop)

(push)
(assert (not (= (not p) (not (not q)))))
(assert p)
(check-sat)
(pop)

(push)
(assert (not (= (not (not q)) (not p))))
(assert p)
(check-sat)
(pop)

(push)
(assert (not (= (not (not p)) (not (not (not q))))))
(assert p)
(check-sat)
(pop)

(push)
(assert (not (= (not (not (not q))) (not (not p)))))
(assert p)
(check-sat)
(pop)