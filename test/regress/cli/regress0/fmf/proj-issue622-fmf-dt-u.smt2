; EXPECT: sat
(set-logic DT)
(set-option :finite-model-find true)
(declare-sort u 0)
(declare-datatypes ((d 1) (t 1)) (
(par (p) ((c (s (t p)))))
(par (p) ((g (j p)) (_c (s2 (d p)))))))
(declare-datatypes ((_d 0) (dt 0)) (
((h) (o (s dt) (_s dt) (e u) (se (t u)))) 
((_c (k u)))))
(declare-const x _d)
(assert ((_ is o) x))
(check-sat)
