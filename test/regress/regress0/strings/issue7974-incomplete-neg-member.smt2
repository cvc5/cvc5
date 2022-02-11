; COMMAND-LINE: --incremental
; EXPECT: (error "Strings Incomplete (due to Negative Membership) by default, try --strings-exp option.")
; EXIT: 1
(set-logic ALL)
(declare-fun v () String)
(declare-fun a () Int)
(push)
(assert (and (= 0 (mod 0 a)) (not (str.in_re v (re.* (re.comp (str.to_re "")))))))
(check-sat)
(get-info :reason-unknown)
