; EXPECT: (error "Term of kind * requires the logic to include non-linear arithmetic")
; EXIT: 1
(set-logic QF_LRA)
(set-info :status unknown)
(declare-fun n () Real)

; This example is test that LRA rejects multiplication terms

(assert (= (* n n) 1))

(check-sat)
