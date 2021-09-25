; COMMAND-LINE: -o raw-benchmark
; EXPECT: OPTION "incremental" false;
; EXPECT: OPTION "logic" "ALL";
; EXPECT: DATATYPE
; EXPECT:   nat = succ(pred: nat) | zero
; EXPECT: END;
; EXPECT: x : nat;
; EXPECT: QUERY NOT(is_succ(x)) AND NOT(is_zero(x));
; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
(declare-fun x () nat)
(check-sat-assuming ( (not (and (not ((_ is succ) x)) (not ((_ is zero) x)))) ))
