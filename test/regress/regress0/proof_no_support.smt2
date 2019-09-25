(set-logic ALL)
(set-option :produce-proofs true)

(declare-const a Int)

(assert (and 
          (=
            a
            (+ a a)
          )
          (not (= a 0))
          (not (= a 1))
        )
)

(check-sat)


(exit)
