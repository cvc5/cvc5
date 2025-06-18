; DISABLE-TESTER: dump
; SCRUBBER: grep -o 'Datatype sort Foo is not well-founded'
; EXPECT: Datatype sort Foo is not well-founded
; EXIT: 1
(set-logic ALL)

(declare-datatype Foo ((Bar (x (Array Foo Int)))))
