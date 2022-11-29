; REQUIRES: no-competition
; EXPECT: (error "Parse Error: non_well_founded_dts.smt2:7.490: Datatype sort _dt5 is not well-founded")
; EXIT: 1
; DISABLE-TESTER: dump
(set-option :global-declarations true)
(set-logic QF_ALL)
(declare-datatypes ((_dt0 0) (_dt1 3) (_dt5 0)) (( (_cons10 (_sel6 _dt5) (_sel7 Bool) (_sel8 _dt5) (_sel9 _dt5)) (_cons13 (_sel11 Bool) (_sel12 Bool)))( par ( _p2 _p3 _p4 ) ( (_cons16 (_sel14 _p4) (_sel15 _p2)) (_cons20 (_sel17 _dt0) (_sel18 Bool) (_sel19 Bool)) (_cons26 (_sel21 Bool) (_sel22 Bool) (_sel23 _p4) (_sel24 _p3) (_sel25 _dt5)) (_cons32 (_sel27 _dt5) (_sel28 _p4) (_sel29 _p3) (_sel30 (_dt1 _p2 _p3 _p4)) (_sel31 Bool))) )( (_cons36 (_sel33 Bool) (_sel34 _dt5) (_sel35 _dt0)))))
(declare-const _x38 Int)
(check-sat-assuming ( (xor ((_ divisible 1058814904) _x38) (set.is_singleton (set.inter set.empty set.empty)))))
