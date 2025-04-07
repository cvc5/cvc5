; COMMAND-LINE: --strings-alpha-card=32 --simplification=none
; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun s1 () String)
(assert (= (str.len s1) 1))
(declare-fun s2 () String)
(assert (= (str.len s2) 1))
(declare-fun s3 () String)
(assert (= (str.len s3) 1))
(declare-fun s4 () String)
(assert (= (str.len s4) 1))
(declare-fun s5 () String)
(assert (= (str.len s5) 1))
(declare-fun s6 () String)
(assert (= (str.len s6) 1))
(declare-fun s7 () String)
(assert (= (str.len s7) 1))
(declare-fun s8 () String)
(assert (= (str.len s8) 1))
(declare-fun s9 () String)
(assert (= (str.len s9) 1))
(declare-fun s10 () String)
(assert (= (str.len s10) 1))
(declare-fun s11 () String)
(assert (= (str.len s11) 1))
(declare-fun s12 () String)
(assert (= (str.len s12) 1))
(declare-fun s13 () String)
(assert (= (str.len s13) 1))
(declare-fun s14 () String)
(assert (= (str.len s14) 1))
(declare-fun s15 () String)
(assert (= (str.len s15) 1))
(declare-fun s16 () String)
(assert (= (str.len s16) 1))
(declare-fun s17 () String)
(assert (= (str.len s17) 1))
(declare-fun s18 () String)
(assert (= (str.len s18) 1))
(declare-fun s19 () String)
(assert (= (str.len s19) 1))
(declare-fun s20 () String)
(assert (= (str.len s20) 1))
(declare-fun s21 () String)
(assert (= (str.len s21) 1))
(declare-fun s22 () String)
(assert (= (str.len s22) 1))
(declare-fun s23 () String)
(assert (= (str.len s23) 1))
(declare-fun s24 () String)
(assert (= (str.len s24) 1))
(declare-fun s25 () String)
(assert (= (str.len s25) 1))
(declare-fun s26 () String)
(assert (= (str.len s26) 1))
(declare-fun s27 () String)
(assert (= (str.len s27) 1))
(declare-fun s28 () String)
(assert (= (str.len s28) 1))
(declare-fun s29 () String)
(assert (= (str.len s29) 1))
(declare-fun s30 () String)
(assert (= (str.len s30) 1))
(declare-fun s31 () String)
(assert (= (str.len s31) 1))
(declare-fun s32 () String)
(assert (= (str.len s32) 1))
(declare-fun s33 () String)
(assert (= (str.len s33) 1))
(assert (distinct
s1
s2
s3
s4
s5
s6
s7
s8
s9
s10
s11
s12
s13
s14
s15
s16
s17
s18
s19
s20
s21
s22
s23
s24
s25
s26
s27
s28
s29
s30
s31
s32
s33
))
(check-sat)
