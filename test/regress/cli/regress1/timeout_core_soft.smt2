; COMMAND-LINE: --timeout-core-timeout=200
; REQUIRES: no-competition
; EXPECT: unknown
; EXPECT: (
; EXPECT: tc-A
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
(get-timeout-core-assuming
 (
    (! (not B) :named tc-B)
    (! C :named tc-C)
    (! A :named tc-A)
    (! D :named tc-D)
 )
)
