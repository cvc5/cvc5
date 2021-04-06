; COMMAND-LINE: -q
; EXPECT: sat
; REQUIRES: symfpu
(set-logic ALL)
(set-option :uf-ho true)
(set-option :assign-function-values false)
(set-info :status sat)
(declare-fun b () (_ BitVec 1))
(declare-fun c () (_ BitVec 8))
(declare-fun d () (_ BitVec 23))
(assert (= 0 (fp.to_real (fp b c d))))
(check-sat)
