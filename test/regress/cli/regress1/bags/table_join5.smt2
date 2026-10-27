; REQUIRES: unrestricted-mode
; REQUIRES: no-competition
; DISABLE-TESTER: dump
; EXIT: 1
; SCRUBBER: sed -e 's/Parse Error: [^:]*:[0-9][0-9]*\.[0-9][0-9]*: /Parse Error: /'
; EXPECT: (error "Parse Error: Index in operator of ((_ table.join 0 0 5 0) A B) is out of range for the type of its first argument")
(set-logic HO_ALL)
(declare-fun A () (Table Int Int))
(declare-fun B () (Table Int Int))
(assert (bag.member (tuple 0 0 0 0)
  ((_ table.join 0 0 5 0) A B)))
(check-sat)
