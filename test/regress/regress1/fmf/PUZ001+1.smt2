; COMMAND-LINE: --finite-model-find
; EXPECT: unsat
;%------------------------------------------------------------------------------
;% File     : PUZ001+1 : TPTP v5.4.0. Released v2.0.0.
;% Domain   : Puzzles
;% Problem  : Dreadbury Mansion
;% Version  : Especial.
;%            Theorem formulation : Reduced > Complete.
;% English  : Someone who lives in Dreadbury Mansion killed Aunt Agatha.
;%            Agatha, the butler, and Charles live in Dreadbury Mansion,
;%            and are the only people who live therein. A killer always
;%            hates his victim, and is never richer than his victim.
;%            Charles hates no one that Aunt Agatha hates. Agatha hates
;%            everyone except the butler. The butler hates everyone not
;%            richer than Aunt Agatha. The butler hates everyone Aunt
;%            Agatha hates. No one hates everyone. Agatha is not the
;%            butler. Therefore : Agatha killed herself.

;% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
;%          : [Hah94] Haehnle (1994), Email to G. Sutcliffe
;% Source   : [Hah94]
;% Names    : Pelletier 55 [Pel86]

;% Status   : Theorem
;% Rating   : 0.07 v5.3.0, 0.19 v5.2.0, 0.00 v5.0.0, 0.08 v4.1.0, 0.13 v4.0.0, 0.12 v3.7.0, 0.14 v3.5.0, 0.00 v3.4.0, 0.08 v3.3.0, 0.11 v3.2.0, 0.22 v3.1.0, 0.17 v2.7.0, 0.00 v2.5.0, 0.33 v2.4.0, 0.33 v2.2.1, 0.00 v2.1.0
;% Syntax   : Number of formulae    :   14 (   6 unit)
;%            Number of atoms       :   24 (   5 equality)
;%            Maximal formula depth :    5 (   3 average)
;%            Number of connectives :   16 (   6   ~;   2   |;   1   &)
;%                                         (   0 <=>;   7  =>;   0  <=;   0 <~>)
;%                                         (   0  ~|;   0  ~&)
;%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
;%            Number of functors    :    3 (   3 constant; 0-0 arity)
;%            Number of variables   :   12 (   0 sgn;  10   !;   2   ?)
;%            Maximal term depth    :    1 (   1 average)
;% SPC      : FOF_THM_RFO_SEQ

;% Comments : Modified by Geoff Sutcliffe.
;%          : Also known as "Who killed Aunt Agatha"
;%------------------------------------------------------------------------------
;%----Problem axioms
(set-logic UF)
(set-info :status unsat)
(declare-sort sort__smt2 0)
; functions
(declare-fun agatha__smt2_0 ( ) sort__smt2)
(declare-fun butler__smt2_0 ( ) sort__smt2)
(declare-fun charles__smt2_0 ( ) sort__smt2)
; predicates
(declare-fun lives__smt2_1 ( sort__smt2 ) Bool)
(declare-fun killed__smt2_2 ( sort__smt2 sort__smt2 ) Bool)
(declare-fun hates__smt2_2 ( sort__smt2 sort__smt2 ) Bool)
(declare-fun richer__smt2_2 ( sort__smt2 sort__smt2 ) Bool)

; pel55_1 axiom
(assert (exists ((?X sort__smt2))
    (and (lives__smt2_1 ?X)
        (killed__smt2_2 ?X agatha__smt2_0))))

; pel55_2_1 axiom
(assert (lives__smt2_1 agatha__smt2_0))

; pel55_2_2 axiom
(assert (lives__smt2_1 butler__smt2_0))

; pel55_2_3 axiom
(assert (lives__smt2_1 charles__smt2_0))

; pel55_3 axiom
(assert (forall ((?X sort__smt2))
    (=> (lives__smt2_1 ?X)
        (or (= ?X agatha__smt2_0)
            (= ?X butler__smt2_0)
            (= ?X charles__smt2_0)))))

; pel55_4 axiom
(assert (forall ((?X sort__smt2) (?Y sort__smt2))
    (=> (killed__smt2_2 ?X ?Y)
        (hates__smt2_2 ?X ?Y))))

; pel55_5 axiom
(assert (forall ((?X sort__smt2) (?Y sort__smt2))
    (=> (killed__smt2_2 ?X ?Y)
        (not (richer__smt2_2 ?X ?Y)))))

; pel55_6 axiom
(assert (forall ((?X sort__smt2))
    (=> (hates__smt2_2 agatha__smt2_0 ?X)
        (not (hates__smt2_2 charles__smt2_0 ?X)))))

; pel55_7 axiom
(assert (forall ((?X sort__smt2))
    (=> (not (= ?X butler__smt2_0))
        (hates__smt2_2 agatha__smt2_0 ?X))))

; pel55_8 axiom
(assert (forall ((?X sort__smt2))
    (=> (not (richer__smt2_2 ?X agatha__smt2_0))
        (hates__smt2_2 butler__smt2_0 ?X))))

; pel55_9 axiom
(assert (forall ((?X sort__smt2))
    (=> (hates__smt2_2 agatha__smt2_0 ?X)
        (hates__smt2_2 butler__smt2_0 ?X))))

; pel55_10 axiom
(assert (forall ((?X sort__smt2))
(exists ((?Y sort__smt2)) (not (hates__smt2_2 ?X ?Y)))))

; pel55_11 axiom
(assert (not (= agatha__smt2_0 butler__smt2_0)))

;----This is the conjecture with negated conjecture
; pel55 conjecture
(assert (not (killed__smt2_2 agatha__smt2_0 agatha__smt2_0)))


(check-sat)
