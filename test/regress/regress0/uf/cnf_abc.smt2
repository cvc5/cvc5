(set-logic QF_UF)
(set-info :status unsat)

(declare-sort I 0)
(declare-fun f (I I) I)
(declare-fun a () I)
(declare-fun b () I)
(declare-fun c () I)



(assert
 (or
  (= (f a a) a)
  (= (f a a) b)
  (= (f a a) c)
  ))

(assert
 (or
  (= (f a b) a)
  (= (f a b) b)
  (= (f a b) c)
  ))

(assert
 (or
  (= (f a c) a)
  (= (f a c) b)
  (= (f a c) c)
  ))

(assert
 (or
  (= (f b a) a)
  (= (f b a) b)
  (= (f b a) c)
  ))

(assert
 (or
  (= (f b b) a)
  (= (f b b) b)
  (= (f b b) c)
  ))

(assert
 (or
  (= (f b c) a)
  (= (f b c) b)
  (= (f b c) c)
  ))


(assert
 (or
  (= (f c a) a)
  (= (f c a) b)
  (= (f c a) c)
  ))

(assert
 (or
  (= (f c b) a)
  (= (f c b) b)
  (= (f c b) c)
  ))

(assert
 (or
  (= (f c c) a)
  (= (f c c) b)
  (= (f c c) c)
  ))



(assert
 (or
  (= (f a a) a)
  (= (f b b) a)
  (= (f c c) a)
  ))

(assert
 (or
  (= (f a a) b)
  (= (f b b) b)
  (= (f c c) b)
  ))

(assert
 (or
  (= (f a a) c)
  (= (f b b) c)
  (= (f c c) c)
  ))



(assert
 (or
  (= (f a a) a)
  (= (f b a) b)
  (= (f c a) c)
  ))

(assert
 (or
  (= (f a b) a)
  (= (f b b) b)
  (= (f c b) c)
  ))

(assert
 (or
  (= (f a c) a)
  (= (f b c) b)
  (= (f c c) c)
  ))




(assert (not (= (f a a) a)))
(assert (not (= (f b b) b)))
(assert (not (= (f c c) c)))                


(assert
 (or
  (not (= (f a (f a a)) a))
  (not (= (f a (f a b)) b))
  (not (= (f a (f a c)) c))
  ))

(assert
 (or
  (not (= (f b (f b a)) a)) 
  (not (= (f b (f b b)) b))
  (not (= (f b (f b c)) c))
  ))

(assert
 (or
  (not (= (f c (f c a)) a)) 
  (not (= (f c (f c b)) b))
  (not (= (f c (f c c)) c))
  ))


(assert  (not (= (f a a) (f b a))))
(assert  (not (= (f a a) (f c a))))
(assert  (not (= (f b a) (f c a))))

(assert  (not (= (f a b) (f b b))))
(assert  (not (= (f a b) (f c b))))
(assert  (not (= (f b b) (f c b))))

(assert  (not (= (f a c) (f b c))))
(assert  (not (= (f a c) (f c c))))
(assert  (not (= (f b c) (f c c))))



(check-sat)

(exit)
