; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL_SUPPORTED)
(set-info :status sat)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (and
        (not (sep (not (pto x a)) (pto y b) ))  
        (sep (pto x a) (pto y b))
  )
)

(check-sat)
