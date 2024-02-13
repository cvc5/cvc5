(set-logic QF_SLIA)
(set-info :status unsat)

(declare-fun x () String)

(assert (or
(not (= (str.replace_re x re.none "ABC") x))
(not (= (str.replace_re_all x re.none "ABC") x))
(not (= (str.indexof_re x re.none 0) (- 1)))))

(check-sat)
