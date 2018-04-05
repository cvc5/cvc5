% COMMAND-LINE: --finite-model-find
% EXPECT: sat
(benchmark Isabelle
:status sat
:logic AUFLIA
:extrasorts ( S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11)
:extrafuns (
  (f1 S1)
  (f2 S1)
  (f3 S3 S2 S1)
  (f4 S4 S2 S3)
  (f5 S4)
  (f6 S5 S5 S1)
  (f7 S5)
  (f8 S6 S5 S5)
  (f9 S7 S6)
  (f10 S8 S4 S7)
  (f11 S9 S10 S8)
  (f12 S11 S4 S9)
  (f13 S11)
  (f14 S4)
  (f15 S10)
  (f16 S4)
  (f17 S10 S4)
  (f18 S5 S5 S1)
)
:assumption (not (= f1 f2))
:assumption (forall (?v0 S2) (?v1 S2) (iff (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 ?v1)) )
:assumption (not (= (f6 f7 (f8 (f9 (f10 (f11 (f12 f13 f14) f15) f16)) f7)) f1))
:assumption (= (f6 f7 (f8 (f9 (f10 (f11 (f12 f13 f5) f15) (f17 f15))) f7)) f1)
:assumption (= (f18 f7 (f8 (f9 (f10 (f11 (f12 f13 f14) f15) f16)) f7)) f1)
:assumption (forall (?v0 S5) (= (f6 ?v0 f7) f1) )
:assumption (forall (?v0 S4) (?v1 S10) (?v2 S4) (?v3 S4) (?v4 S10) (?v5 S4) (iff (= (f10 (f11 (f12 f13 ?v0) ?v1) ?v2) (f10 (f11 (f12 f13 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5)))) )
:assumption (forall (?v0 S5) (?v1 S5) (implies (= (f6 ?v0 ?v1) f1) (= (f18 ?v0 ?v1) f1)) )
:assumption (forall (?v0 S5) (?v1 S5) (?v2 S5) (implies (= (f6 ?v0 ?v1) f1) (implies (= (f6 ?v2 ?v0) f1) (= (f6 ?v2 ?v1) f1))) )
:assumption (forall (?v0 S5) (?v1 S7) (?v2 S5) (implies (= (f6 ?v0 (f8 (f9 ?v1) f7)) f1) (implies (= (f6 ?v0 ?v2) f1) (= (f6 ?v0 (f8 (f9 ?v1) ?v2)) f1))) )
:assumption (forall (?v0 S5) (?v1 S7) (?v2 S5) (implies (= (f6 ?v0 (f8 (f9 ?v1) ?v2)) f1) (and (= (f6 ?v0 (f8 (f9 ?v1) f7)) f1) (= (f6 ?v0 ?v2) f1))) )
:assumption (forall (?v0 S5) (?v1 S4) (?v2 S10) (?v3 S4) (?v4 S4) (implies (= (f6 ?v0 (f8 (f9 (f10 (f11 (f12 f13 ?v1) ?v2) ?v3)) f7)) f1) (implies (forall (?v5 S2) (?v6 S2) (implies (= (f3 (f4 ?v3 ?v5) ?v6) f1) (= (f3 (f4 ?v4 ?v5) ?v6) f1))) (= (f6 ?v0 (f8 (f9 (f10 (f11 (f12 f13 ?v1) ?v2) ?v4)) f7)) f1))) )
:assumption (forall (?v0 S5) (?v1 S4) (?v2 S10) (?v3 S4) (?v4 S4) (implies (= (f6 ?v0 (f8 (f9 (f10 (f11 (f12 f13 ?v1) ?v2) ?v3)) f7)) f1) (implies (forall (?v5 S2) (?v6 S2) (implies (= (f3 (f4 ?v4 ?v5) ?v6) f1) (= (f3 (f4 ?v1 ?v5) ?v6) f1))) (= (f6 ?v0 (f8 (f9 (f10 (f11 (f12 f13 ?v4) ?v2) ?v3)) f7)) f1))) )
:formula true)
; solver: z3
; timeout: 5.0
; random seed: 1
; arguments:
; DISPLAY_PROOF=true
; PROOF_MODE=2
; -rs:1
; MODEL=true
; -smt
