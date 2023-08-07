; EXPECT: true
; EXPECT: false
(set-logic ALL)
(declare-fun A () Bool)
(declare-fun B () Bool)
(find-synth :enum ((Start Bool)) ((Start Bool (true false))))
(find-synth-next)
