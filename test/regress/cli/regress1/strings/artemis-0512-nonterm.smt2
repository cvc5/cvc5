(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-option :strings-exp true)
(set-info :status unsat)

(declare-const Y String)
(assert
  (or
    (= Y "01")
    (= Y "02")
    (= Y "03")
    (= Y "04")
    (= Y "05")
    (= Y "06")
    (= Y "07")
    (= Y "08")
    (= Y "09")
    (= Y "10")
    (= Y "11")
    (= Y "12")
  )
)
 
(assert (= (<= (str.to_int Y) 31) false))
 
(check-sat)
 
