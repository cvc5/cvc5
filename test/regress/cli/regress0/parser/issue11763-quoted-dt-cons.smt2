; EXPECT: sat
(set-logic QF_UFDTLIA)
(declare-datatype MyList (par (T) ((nelem) (|cons| (hd T) (tl (MyList T))))))

(declare-fun a () (MyList Int))
(assert (> (hd a) 50))
(assert (not (and
  ((_ is |cons|) a) (not ((_ is nelem) a))
)))
(check-sat)
