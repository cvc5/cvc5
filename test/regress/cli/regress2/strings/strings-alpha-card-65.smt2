; COMMAND-LINE: --strings-alpha-card=64 --simplification=none
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
(declare-fun s34 () String)
(assert (= (str.len s34) 1))
(declare-fun s35 () String)
(assert (= (str.len s35) 1))
(declare-fun s36 () String)
(assert (= (str.len s36) 1))
(declare-fun s37 () String)
(assert (= (str.len s37) 1))
(declare-fun s38 () String)
(assert (= (str.len s38) 1))
(declare-fun s39 () String)
(assert (= (str.len s39) 1))
(declare-fun s40 () String)
(assert (= (str.len s40) 1))
(declare-fun s41 () String)
(assert (= (str.len s41) 1))
(declare-fun s42 () String)
(assert (= (str.len s42) 1))
(declare-fun s43 () String)
(assert (= (str.len s43) 1))
(declare-fun s44 () String)
(assert (= (str.len s44) 1))
(declare-fun s45 () String)
(assert (= (str.len s45) 1))
(declare-fun s46 () String)
(assert (= (str.len s46) 1))
(declare-fun s47 () String)
(assert (= (str.len s47) 1))
(declare-fun s48 () String)
(assert (= (str.len s48) 1))
(declare-fun s49 () String)
(assert (= (str.len s49) 1))
(declare-fun s50 () String)
(assert (= (str.len s50) 1))
(declare-fun s51 () String)
(assert (= (str.len s51) 1))
(declare-fun s52 () String)
(assert (= (str.len s52) 1))
(declare-fun s53 () String)
(assert (= (str.len s53) 1))
(declare-fun s54 () String)
(assert (= (str.len s54) 1))
(declare-fun s55 () String)
(assert (= (str.len s55) 1))
(declare-fun s56 () String)
(assert (= (str.len s56) 1))
(declare-fun s57 () String)
(assert (= (str.len s57) 1))
(declare-fun s58 () String)
(assert (= (str.len s58) 1))
(declare-fun s59 () String)
(assert (= (str.len s59) 1))
(declare-fun s60 () String)
(assert (= (str.len s60) 1))
(declare-fun s61 () String)
(assert (= (str.len s61) 1))
(declare-fun s62 () String)
(assert (= (str.len s62) 1))
(declare-fun s63 () String)
(assert (= (str.len s63) 1))
(declare-fun s64 () String)
(assert (= (str.len s64) 1))
(declare-fun s65 () String)
(assert (= (str.len s65) 1))
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
s34
s35
s36
s37
s38
s39
s40
s41
s42
s43
s44
s45
s46
s47
s48
s49
s50
s51
s52
s53
s54
s55
s56
s57
s58
s59
s60
s61
s62
s63
s64
s65
))
(check-sat)
