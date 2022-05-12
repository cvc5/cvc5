; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(set-option :sygus-inference true)
(set-option :sygus-simple-sym-break none)
(set-option :sygus-sym-break-lazy false)
(set-option :sygus-sym-break-rlv false)
(set-info :status sat)
(declare-fun s () String)
(assert (distinct s ""))
(check-sat)
