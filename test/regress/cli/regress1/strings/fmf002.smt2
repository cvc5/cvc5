(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-option :strings-exp true)
(set-option :strings-fmf true)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

(assert (str.in_re x
                (re.+ (re.range "a" "c"))
				                ))

(assert (= x (str.++ y "c" z "b")))
(assert (> (str.len z) 1))

(check-sat)
