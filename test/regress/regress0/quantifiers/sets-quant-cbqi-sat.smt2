(set-logic ALL)
(set-info :status sat)
(declare-datatypes ((E 0))
	(((p (fst-p Int) (snd-p Int)) (q (fst-q Int))))
)

(declare-const S (Set E))

(define-fun I1 ((a Int) (b Int) (c Int)) Bool
	    (= S (union (singleton (p a b)) (singleton (q c))))
)

(define-fun I2 ((a Int) (b Int) (c Int)) Bool
	    (= S (insert (q a) (q b) (singleton (q c))))
)

(assert 
	(and 
	     (exists ((x Int)) (I1 x x x))
	     (not (exists ((x Int) (y Int) (z Int)) (I2 x y z)))
	)
)
(check-sat)
