;COMMAND-LINE: --check-proofs
;EXIT: 1
;EXPECT: (error "Error in option parsing: Proofs are only supported for sub-logics of QF_AUFBVLIA.")
(set-logic ALL)

(declare-const a Int)

(assert (and 
          (=
            a
            (* a a)
          )
          (not (= a 0))
          (not (= a 1))
        )
)

(check-sat)



