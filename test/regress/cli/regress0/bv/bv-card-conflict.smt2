; EXPECT: unsat
(set-logic ALL)
(declare-const a (_ BitVec 2))
(declare-const b (_ BitVec 2))
(declare-const c (_ BitVec 2))
(declare-const d (_ BitVec 2))
(declare-const e (_ BitVec 2))
(assert (distinct a b c d e))
(check-sat)
