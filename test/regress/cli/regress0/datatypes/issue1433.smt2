; EXPECT: sat
(set-logic QF_UFDTLIA)
(set-info :status sat)
(declare-datatype MyList (par (T) ((nelem) (cons (hd T) (tl (MyList T))))))

(declare-fun a () (MyList Int))
(assert (> (hd a) 50))
(check-sat)
