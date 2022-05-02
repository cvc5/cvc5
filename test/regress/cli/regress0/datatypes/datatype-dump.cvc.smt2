; COMMAND-LINE: -o raw-benchmark
; EXPECT: (set-logic ALL)
; EXPECT: (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
; EXPECT: (declare-fun x () nat)
; EXPECT: (check-sat-assuming ( (not (and (not ((_ is succ) x)) (not ((_ is zero) x)))) ))
; EXPECT: sat
(set-logic ALL)
(declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
(declare-fun x () nat)
(check-sat-assuming ( (not (and (not ((_ is succ) x)) (not ((_ is zero) x)))) ))
