; COMMAND-LINE: -mi
; EXPECT: sat
; EXPECT: unsat

(set-logic ALL_SUPPORTED)

; must make parts 1 through 6 with different deadlines

; part 1 must be available for part 2
; parts 3 and 4 must be available for part 5
; all parts must be available for part 6

; start/complete is the timestep when a part is started/finished
(declare-fun start (Int) Int)
(declare-fun complete (Int) Int)

(define-fun before ((i Int) (j Int)) Bool (< (complete i) (start j)))

(assert (before 1 2))
(assert (before 3 5))
(assert (before 4 5))
(assert (before 1 6))
(assert (before 2 6))
(assert (before 3 6))
(assert (before 4 6))
(assert (before 5 6))

; part 1 takes 2 units of time
; part 2 takes 3
; part 3 takes 3
; part 4 takes 1
; part 5 takes 2
; part 6 takes 1

(define-fun requires ((i Int) (j Int)) Bool (= (complete i) (+ (start i) j)))

(assert (requires 1 2))
(assert (requires 2 3))
(assert (requires 3 3))
(assert (requires 4 1))
(assert (requires 5 2))
(assert (requires 6 1))

(assert (>= (start 1) 0))
(assert (>= (start 2) 0))
(assert (>= (start 3) 0))
(assert (>= (start 4) 0))
(assert (>= (start 5) 0))
(assert (>= (start 6) 0))

(define-fun cost () Int (complete 6))

(define-fun parallel ((t Int)) Int
            (+ (ite (<= (start 1) t (complete 1)) 1 0)
               (ite (<= (start 2) t (complete 2)) 1 0)
               (ite (<= (start 3) t (complete 3)) 1 0)
               (ite (<= (start 4) t (complete 4)) 1 0)
               (ite (<= (start 5) t (complete 5)) 1 0)
               (ite (<= (start 6) t (complete 6)) 1 0)))

(declare-fun cost2 () Int)
(assert (= cost2 cost))

(declare-fun max-parallel () Int)
(assert (forall ((t Int)) (=> (<= 0 t cost2) (>= max-parallel (parallel t)))))

(check-sat)
;(get-model)
;(get-value (cost2))
;(get-value ((parallel 1)))
;(get-value ((=> (<= 0 1 cost2) (>= max-parallel (parallel 1)))))

(assert (< cost 8))

(check-sat)
