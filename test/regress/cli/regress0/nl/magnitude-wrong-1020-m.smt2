; COMMAND-LINE: --nl-ext=full
; EXPECT: sat
(set-logic QF_NRA)
(set-info :source |
From termination analysis of term rewriting.

Submitted by Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :smt-lib-version 2.6)
(set-info :category "industrial")
(set-info :status sat)
  (define-fun x6 () Real
    1.0)
  (define-fun x13 () Real
    (/ 1.0 32.0))
  (define-fun x3 () Real
    1.0)
  (define-fun x10 () Real
    1.0)
  (define-fun x0 () Real
    1.0)
  (define-fun x17 () Real
    3.0)
  (define-fun x7 () Real
    (/ 1.0 4.0))
  (define-fun x14 () Real
    (/ 3.0 4.0))
  (define-fun x4 () Real
    2.0)
  (define-fun x11 () Real
    1.0)
  (define-fun x1 () Real
    (/ 3.0 2.0))
  (define-fun x18 () Real
    0.0)
  (define-fun x8 () Real
    1.0)
  (define-fun x15 () Real
    1.0)
  (define-fun x5 () Real
    1.0)
  (define-fun x12 () Real
    2.0)
  (define-fun x2 () Real
    1.0)
  (define-fun x9 () Real
    0.0)
  (define-fun x16 () Real
    (/ 1.0 4.0))

(assert (>= x6 0))
(assert (>= x13 0))
(assert (>= x3 0))
(assert (>= x10 0))
(assert (>= x0 0))
(assert (>= x17 0))
(assert (>= x7 0))
(assert (>= x14 0))
(assert (>= x4 0))
(assert (>= x11 0))
(assert (>= x1 0))
(assert (>= x18 0))
(assert (>= x8 0))
(assert (>= x15 0))
(assert (>= x5 0))
(assert (>= x12 0))
(assert (>= x2 0))
(assert (>= x9 0))
(assert (>= x16 0))
(assert (let ((?v_0 (+ x0 (* x2 x3))) (?v_2 (* x2 x4)) (?v_1 (+ x5 (* x6 x7))) (?v_4 (* x12 x3))) (let ((?v_3 (+ (+ x10 (* x11 x3)) ?v_4)) (?v_6 (* x11 x4)) (?v_7 (* x12 x4)) (?v_5 (+ (+ x10 (* x11 x7)) ?v_4))) (let ((?v_17 (and (and (and (and (and (> ?v_0 x0) (>= ?v_0 x0)) (>= ?v_2 x2)) (and (and (and (> ?v_0 ?v_1) (>= ?v_0 ?v_1)) (>= x1 (* x6 x8))) (>= ?v_2 (* x6 x9)))) (and (and (and (> ?v_3 x0) (>= ?v_3 x0)) (>= ?v_6 x1)) (>= ?v_7 x2))) (and (and (and (> ?v_3 ?v_5) (>= ?v_3 ?v_5)) (>= ?v_6 (* x11 x8))) (>= ?v_7 (+ (* x11 x9) ?v_7))))) (?v_8 (+ x13 (* x14 x3))) (?v_9 (+ x7 (* x9 x15))) (?v_11 (+ x13 (* x14 x7))) (?v_10 (+ x7 (* x9 x3))) (?v_13 (* x18 x3))) (let ((?v_12 (+ (+ x16 (* x17 x15)) ?v_13)) (?v_15 (+ x3 (* x4 (+ (+ x16 (* x17 x7)) ?v_13)))) (?v_14 (+ (+ x16 (* x17 x3)) ?v_13)) (?v_16 (* x18 x4))) (and (and (and (and (and (and ?v_17 (and (and (> ?v_8 0) (>= ?v_8 0)) (>= (* x14 x4) 1))) (and (and (> ?v_9 0) (>= ?v_9 0)) (>= x8 1))) (and (and (and (> ?v_10 ?v_11) (>= ?v_10 ?v_11)) (>= x8 (* x14 x8))) (>= (* x9 x4) (* x14 x9)))) (and (> ?v_12 x15) (>= ?v_12 x15))) (and (and (and (> ?v_14 ?v_15) (>= ?v_14 ?v_15)) (>= (* x17 x4) (* x4 (* x17 x8)))) (>= ?v_16 (* x4 (+ (* x17 x9) ?v_16))))) ?v_17))))))
(check-sat)
