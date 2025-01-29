; COMMAND-LINE: --produce-proofs --proof-check=eager
; EXPECT: sat
(set-logic QF_FFDT)
(declare-datatypes ((d 0)) (((c (s Bool)) (_c (_s d)) (o (e Bool) (se Bool)))))
(declare-const x d)
(check-sat-assuming ((or ((_ is c) ((_ update e) x false)) (= x (_s x)))))
