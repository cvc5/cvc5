; COMMAND-LINE: --timeout-core-timeout=200 --print-cores-full
; REQUIRES: no-competition
; EXPECT: unknown
; EXPECT: (
; EXPECT: A
; EXPECT: )
(set-logic ALL)
(set-option :produce-unsat-cores true)
(declare-fun A () Bool)
(declare-fun B () Bool)
(declare-fun C () Bool)
(declare-fun D () Bool)
(declare-fun x () Int)
(assert (=> (or A B) (= (* x x x) 564838384999)))
(assert (=> D (> x 0)))
; making A true forces the equality to be asserted, making the problem hard
(get-timeout-core
 (
    (not B)
    C
    A
    D
 )
)
