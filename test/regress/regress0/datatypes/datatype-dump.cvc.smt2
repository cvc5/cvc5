; COMMAND-LINE: -o raw-benchmark
; EXPECT-ERROR: (set-option :incremental false)
; EXPECT-ERROR: (set-logic ALL)
; EXPECT-ERROR: (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
; EXPECT-ERROR: (declare-fun x () nat)
; EXPECT-ERROR: (check-sat-assuming ( (not (and (not ((_ is succ) x)) (not ((_ is zero) x)))) ))
; EXPECT: sat
(set-logic ALL)
(declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
(declare-fun x () nat)
(check-sat-assuming ( (not (and (not ((_ is succ) x)) (not ((_ is zero) x)))) ))
