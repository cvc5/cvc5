; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun b () (_ BitVec 4) #b0101)
; EXPECT: )
; EXPECT: ((n1 true))
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun b () Bool true)
; EXPECT: )
; EXPECT: ((n2 true))
; EXPECT: unsat
; EXPECT: (
; EXPECT: )
(set-option :produce-models true)
(set-option :produce-assignments true)
(set-option :produce-unsat-cores true)
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(check-sat)
(reset-assertions)
(declare-const b (_ BitVec 4))
(assert (! (= b #b0101) :named n1))
(check-sat)
(get-model)
(get-assignment)
(reset-assertions)
(declare-const b Bool)
(assert (! b :named n2))
(check-sat)
(get-model)
(get-assignment)
(reset-assertions)
(assert (= #x1 #x2))
(check-sat)
(get-unsat-core)
