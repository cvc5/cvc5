; REQUIRES: cocoa
; EXPECT: unsat
; COMMAND-LINE: --ff-solver gb
; COMMAND-LINE: --ff-solver split

; original:
; ### start
; s = Solver()
;
; mac1,mac2,m1,m2,k1,k2,d = FiniteFieldElems('mac1 mac2 m1 m2 k1 k2 d', 7)
;
; s.add(mac1 == k1 + (d * m1))
; s.add(mac2 == k2 + (d * m2))
; s.add(mac1 + mac2 != (k1 + k2) + (d * (m1 + m2)))
; s.check()
; ### end

; translated into SMT2:
(set-logic QF_FF)
(define-sort F () (_ FiniteField 7))
(declare-const mac1 F)
(declare-const mac2 F)
(declare-const m1 F)
(declare-const m2 F)
(declare-const k1 F)
(declare-const k2 F)
(declare-const d F)

(assert (= mac1 (ff.add k1 (ff.mul d m1))))
(assert (= mac2 (ff.add k2 (ff.mul d m2))))
(assert (not (= (ff.add mac1 mac2) (ff.add k1 k2 (ff.mul d (ff.add m1 m2))))))
(check-sat)

