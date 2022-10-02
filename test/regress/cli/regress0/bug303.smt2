(set-logic QF_UFLIA)
(set-info :status unsat)

;; don't use a datatypes for currently focusing in uf
(declare-sort list 0)

(declare-fun cons (Int list) list)
(declare-fun nil () list)

;;define length
(declare-fun length (list) Int)

(assert (= (length nil) 0))

(declare-fun one_cons (list) list)

(assert (= (length (cons 1 nil)) (+ 1 (length nil))))
(assert (= (one_cons nil) (cons 1 nil)))
(assert (not (= (length (one_cons nil)) 1)))

(check-sat)

(exit)
