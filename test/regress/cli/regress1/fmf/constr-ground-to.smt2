; COMMAND-LINE: --fmf-fun
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic UFDTLIA)
(declare-datatypes ((Term 0) (IntList 0)) (
	(
		(str (sv IntList))
	)
	(
		(sn)
		(sc (sh Int) (st IntList))
	)
))
(declare-const t Term)
(assert (
	and
	((_ is str) t)
	((_ is sc) (sv t))
	((_ is sc) (st (sv t)))
	((_ is sc) (st (st (sv t))))
	((_ is sc) (st (st (st (sv t)))))
	((_ is sc) (st (st (st (st (sv t))))))
	((_ is sc) (st (st (st (st (st (sv t)))))))
	((_ is sc) (st (st (st (st (st (st (sv t))))))))
	((_ is sc) (st (st (st (st (st (st (st (sv t)))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (sv t))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (sv t)))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (st (st (sv t)))))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t)))))))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t)))))))))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t)))))))))))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t)))))))))))))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t)))))))))))))))))))))))
	((_ is sc) (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (st (sv t))))))))))))))))))))))))
))
(check-sat)
