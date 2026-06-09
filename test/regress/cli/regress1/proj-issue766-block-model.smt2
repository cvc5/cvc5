; COMMAND-LINE: -q
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(set-option :global-declarations true)
(set-option :produce-models true)
(set-option :incremental true)
(declare-const _x29 (Seq String) )
(assert (distinct _x29 (as seq.empty (Seq String))))
(assert ((_ divisible 40577120) (seq.len _x29)))
(check-sat)
(block-model-values (
  (seq.len _x29)
  (as seq.empty (Seq String))
  re.allchar
  (as seq.empty (Seq String))
  re.allchar
))
(check-sat)
