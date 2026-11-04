; EXPECT: unsat
; Rewrite::UPD_REV must have a complete proof, via RARE rule str-update-rev.
(set-logic ALL)
(declare-const s String)
(declare-const t String)
(declare-const u String)
(declare-const n Int)
(assert (distinct (str.update (str.rev s) 0 "a")
                  (str.rev (str.update s (- (str.len s) 1) "a"))))
(check-sat)
