; DISABLE-TESTER: dump
; COMMAND-LINE: --produce-models
; EXPECT: sat
; EXPECT: (((f (as @Foo_0 Foo)) 3))
(set-logic ALL)
(set-option :produce-models true)
(declare-sort Foo 0)
(declare-fun f (Foo) Int)
(assert (exists ((x Foo)) (= (f x) 3)))
(check-sat)
(get-value ((f @Foo_0)))
