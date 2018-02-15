; COMMAND-LINE: --finite-model-find --fmf-bound-int
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(set-info :status sat)
(set-option :incremental true)
(declare-fun P (Int) Bool)
(declare-fun ten () Int)

(assert (forall ((x Int)) (=> (<= 1 x ten) (P x))))

(push)
(assert (= ten 10))

(check-sat)
(pop)
