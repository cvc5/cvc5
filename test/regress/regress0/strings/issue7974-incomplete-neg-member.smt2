; COMMAND-LINE: --incremental
; EXPECT-ERROR: Strings Incomplete (due to Negative Membership) by default, try --strings-exp option.
; EXPECT: unknown
; EXPECT: (:reason-unknown incomplete)
(set-logic ALL)
(declare-fun v () String)
(declare-fun a () Int)
(push)
(assert (and (= 0 (mod 0 a)) (not (str.in_re v (re.* (re.comp (str.to_re "")))))))
(check-sat)
(get-info :reason-unknown)
