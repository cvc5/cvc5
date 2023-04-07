; COMMAND-LINE: --simplification=none --unsat-cores-mode=sat-proof
; EXPECT: a0
; EXPECT: a1
; EXPECT: a2
; EXPECT: a3
; EXPECT: a4
; EXPECT: )
; EXPECT: (
; EXPECT: (or (= (f a c) (f b d)) (not (= a b)) (not (= c d)))
; EXPECT: )
;
;; This will remove the initial "unsat" and "(" lines of the output, then order the unsat core (next 5 lines) and print the rest as is (the unsat core lemmas).
; SCRUBBER: tail -n +3 | awk -v n=5 '{if(NR<=n){print $0 | "sort"}else{print $0}}' | cat


(set-logic QF_UF)
(set-option :produce-unsat-cores true)

(declare-sort U 0)
(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-fun f (U U) U)

(assert (! (= a b) :named a0))
(assert (! (= c d) :named a1))
(assert (! (and p1 true) :named a2))
(assert (! (or (not p1) (and p2 p3)) :named a3))
(assert (! (or (not p3) (not (= (f a c) (f b d)))) :named a4))

(check-sat)

(get-unsat-core)
(get-unsat-core-lemmas)
