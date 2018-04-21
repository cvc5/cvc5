(set-logic QF_S)
(set-option :strings-exp true)
(set-info :status unsat)

(declare-const buff String)
(declare-const pass_mem String)
(assert (= (str.len buff) 4))
(assert (= (str.len pass_mem) 1))

(assert (str.in.re (str.++ buff pass_mem) (re.+ (str.to.re "A"))))

(assert (str.contains buff "<"))

(check-sat)
