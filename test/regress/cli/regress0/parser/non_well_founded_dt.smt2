; REQUIRES: no-competition
; SCRUBBER: grep -o "Datatype sort _dt5 is not well-founded"
; EXPECT: Datatype sort _dt5 is not well-founded
; EXIT: 1
; DISABLE-TESTER: dump
(set-option :global-declarations true)
(set-logic QF_ALL)
(declare-datatype _dt5 ((_cons36 (_sel33 Bool) (_sel34 _dt5) (_sel35 _dt5))))
(declare-const _x38 Int)
(check-sat-assuming ( (xor ((_ divisible 1058814904) _x38) (set.is_singleton (set.inter set.empty set.empty)))))
