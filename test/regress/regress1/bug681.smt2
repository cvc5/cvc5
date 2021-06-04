; EXIT: 1
; EXPECT: (error "Array theory solver does not yet support write-chains connecting two different constant arrays")
(set-logic ALL)
(declare-fun start!1 () Bool)

(assert start!1)

(declare-fun lt!2 () Bool)

(assert (=> start!1 (not lt!2)))

(declare-datatypes ((Option!3 0)) (((None!1) (Some!1 (v!18 Int)))))

(declare-datatypes ((Method!1 0)) (((Method!2 (initials!1 (Array Option!3 Int))))))

(declare-fun lambda!2 () (Array Int Method!1))

(declare-fun isValidStep!1 ((Array Int Method!1) (Array Int Option!3) (Array Int Option!3) Int Int Option!3) Bool)

(declare-fun control!1 () (Array Int Option!3))

(declare-fun next_control!0 () (Array Int Option!3))

(assert (=> start!1 (= lt!2 (not (isValidStep!1 lambda!2 control!1 next_control!0 0 0 (Some!1 5))))))

(declare-fun d!1 () Bool)

(assert (=> d!1 (= (isValidStep!1 lambda!2 control!1 next_control!0 0 0 (Some!1 5)) (= next_control!0 (store control!1 0 (Some!1 (select (initials!1 (select lambda!2 0)) (Some!1 5))))))))

(declare-fun methods!1 (Int) Method!1)

(assert (=> d!1 (= (select lambda!2 0) (methods!1 0))))

(declare-fun b_lambda!1 () Bool)

(assert (=> (not b_lambda!1) (not d!1)))

(assert (=> start!1 d!1))

(declare-fun d!3 () Bool)

(assert (=> d!3 (= control!1 ((as const (Array Int Option!3)) None!1))))

(assert (=> start!1 d!3))

(declare-fun d!5 () Bool)

(assert (=> d!5 (= next_control!0 (store ((as const (Array Int Option!3)) None!1) 0 (Some!1 0)))))

(assert (=> start!1 d!5))

(assert true)

(check-sat)
