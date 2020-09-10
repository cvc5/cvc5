(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-option :strings-exp true)
(set-option :strings-fmf true)
(set-info :status sat)
(declare-fun z () String)
(declare-fun n () Int)
(declare-fun y () String)

;(define-fun z () String "AB")
;(define-fun n () Int 0)
;(define-fun y () String "B")

(assert (not (=
(str.substr (str.substr z 0 n) 0 (str.indexof (str.substr z 0 n) y 0))
(str.substr z 0 (str.indexof z y 0))
)))

(check-sat)
