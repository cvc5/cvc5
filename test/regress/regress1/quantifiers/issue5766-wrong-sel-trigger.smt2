; COMMAND-LINE: --sygus-inst -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-datatypes ((a 0))
  (((b (c a) (d a)) (n (o a)) (e (f a) (g a)) (h (i (_ BitVec 1))))))
(declare-fun j (a) Bool)
(declare-fun k (a) a)
(declare-fun l () a)
(assert (forall ((m a)) (=> ((_ is h) m) (j (ite ((_ is b) m) (b m m)
  (ite ((_ is e) m) (e m m) (ite ((_ is b) m) (e m m) (ite (xor ((_
  is n) m) ((_ is e) m)) (b m m) (ite (xor ((_ is n) m) ((_ is n) (o
  m))) (k (o m)) (ite ((_ is n) m) m (ite ((_ is h) m) m
  l)))))))))))
(check-sat)
