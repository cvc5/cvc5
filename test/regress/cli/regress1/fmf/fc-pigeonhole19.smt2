(set-logic UFC)
(set-info :status unsat)

(declare-sort P 0)
(declare-sort H 0)

(declare-fun p () P)
(declare-fun h () H)

; pigeonhole using native cardinality constraints
(assert (_ fmf.card P 19))
(assert (not (_ fmf.card P 18)))
(assert (_ fmf.card H 18))
(assert (not (_ fmf.card H 17)))

; each pigeon has different holes
(declare-fun f (P) H)
(assert (forall ((p1 P) (p2 P)) (=> (not (= p1 p2)) (not (= (f p1) (f p2))))))

(check-sat)
