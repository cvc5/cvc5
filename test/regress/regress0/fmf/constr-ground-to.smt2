; COMMAND-LINE: --fmf-fun --lang=smt2.5
; EXPECT: sat
(set-logic UFDTLIA)
(declare-datatypes () (
	(
		Term
		(str (sv IntList))
	)
	(
		IntList
		(sn)
		(sc (sh Int) (st IntList))
	)
))
(declare-const t Term)
(assert (
	and
	(is-str t)
	(is-sc (sv t))
	(is-sc (st (sv t)))
	(is-sc (st (st (sv t))))
	(is-sc (st (st (st (sv t)))))
	(is-sc (st (st (st (st (sv t))))))
	(is-sc (st (st (st (st (st (sv t)))))))
	(is-sc (st (st (st (st (st (st (sv t))))))))
	(is-sc (st (st (st (st (st (st (st (sv t)))))))))
	(is-sc (st (st (st (st (st (st (st (st (sv t))))))))))
	(is-sc (st (st (st (st (st (st (st (st (st (sv t)))))))))))
	(is-sc (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))
	(is-sc (st (st (st (st (st (st (st (st (st (st (st (sv t)))))))))))))
	(is-sc (st (st (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))))
	(is-sc (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t)))))))))))))))
	(is-sc (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))))))
	(is-sc (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t)))))))))))))))))
	(is-sc (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))))))))
	(is-sc (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t)))))))))))))))))))
	(is-sc (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))))))))))
	(is-sc (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t)))))))))))))))))))))
	(is-sc (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))))))))))))
	(is-sc (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t)))))))))))))))))))))))
 	(is-sc (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))))))))))))))
))
(check-sat)
