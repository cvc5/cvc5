; EXPECT: sat
(set-logic QF_UF)
(set-option :global-declarations true)
(set-option :produce-models true)
(declare-const _x0 Bool)
(declare-const _x1 Bool)
(check-sat)
(block-model :literals)
