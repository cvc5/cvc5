; COMMAND-LINE: --decision=stoponly --sygus-inference=try -q
; EXPECT: sat
(set-logic ALL)
(declare-const v3 Bool)
(declare-const r1 Real)
(declare-const r7 Real)
(declare-const r16 Real)
(declare-const arr0 (Array Bool (Array Real Real)))
(declare-const v15 Bool)
(declare-const r21 Real)
(assert
  (or (not v15)
      (distinct 0.75 r21 (select (select arr0 v3) r16))
      (<= 5943.0 r1 r7)))
(check-sat)
