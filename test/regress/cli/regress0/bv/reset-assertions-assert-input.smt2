; COMMAND-LINE: -i --bv-solver=bitblast --bv-assert-input
(set-logic QF_BV)
(set-option :global-declarations true)

(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(declare-const d (_ BitVec 8))

(assert (distinct (bvadd a d) (bvadd b c)))
(set-info :status sat)
(check-sat)

(reset-assertions)

(assert (= (bvadd a d) (bvadd b c)))
(set-info :status sat)
(check-sat)
