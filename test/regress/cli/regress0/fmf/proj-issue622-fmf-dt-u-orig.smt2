; EXPECT: sat
(set-logic DT)
(set-option :finite-model-find true)
(declare-sort u 0)
(declare-datatypes ((d 1) (t 2)) ((par (p) ((c (s (t p p))))) (par (p p) ((c (d p)) (_c (s (d p)))))))
(declare-datatypes ((_d 0) (dt 0)) (((c) (o (s dt) (_s dt) (e u) (se (t u u)))) ((_c (_s u)))))
(declare-const x _d)
(assert ((_ is o) x))
(check-sat)
