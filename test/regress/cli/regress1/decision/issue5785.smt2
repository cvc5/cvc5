; COMMAND-LINE: --fmf-fun -i --decision=justification
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALRA)
(set-option :fmf-fun true)
(declare-fun v2 () Bool)
(declare-sort S0 0)
(declare-fun arr--1494941102250395870_2811598136228140380-0 () (Array Bool S0))
(declare-fun arr-2811598136228140380_-1494941102250395870-0 () (Array S0 Bool))
(push)
(assert (select arr-2811598136228140380_-1494941102250395870-0 (select arr--1494941102250395870_2811598136228140380-0 false)))
(push)
(pop)
(pop)
(assert (select arr-2811598136228140380_-1494941102250395870-0 (select (store arr--1494941102250395870_2811598136228140380-0 v2 (select arr--1494941102250395870_2811598136228140380-0 true)) true)))
(check-sat)
