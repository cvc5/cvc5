(set-logic UFDTLIRA)
(set-option :fmf-bound true)
(set-option :finite-model-find true)
(set-option :produce-models true)
(set-info :status sat)

;;; ----- Agents (Nodes, Packets, Channels)

(declare-datatype NodeMobile ((Rnode)))
(declare-datatype NodeInfra ((Anode) (Bnode) (Cnode)))
(declare-datatype NodeBase ((Dnode)))
(declare-datatype Node ((mobile (mnode NodeMobile)) (infra (inode NodeInfra)) (base (bnode NodeBase))))

(define-fun R () Node (mobile Rnode))
(define-fun A () Node (infra Anode))
(define-fun B () Node (infra Bnode))
(define-fun C () Node (infra Cnode))
(define-fun D () Node (base Dnode))

(declare-datatype Packet ((P1)))

(declare-datatype Channel ((Ch1) (Ch2) (Ch3)))


;;; ----- The global state 

; for each packet, have we received that packet?
(declare-fun GlobalState_prcv (Node Packet Int) Bool)

; for each node, its energy consumption up to that time
(declare-fun GlobalState_energy (Node Int) Real)

;;; ----- Action, Conditionals

(declare-datatype Action
(
(act_idle)
(act_send (_dst Node) (_pck Packet) (_chn Channel))
))

(declare-datatype Condition
(
(ctrue)
(check_rcv (_rcv_pck Packet))
))

; --- does a condition hold for a Node at a given time, given the global state
(define-fun get-condition-holds ((c Condition) (n Node) (t Int)) Bool
  (ite ((_ is check_rcv) c)
    (GlobalState_prcv n (_rcv_pck c) t)
  (ite ((_ is ctrue) c) 
    true
  ; ((_ is cfalse) c)
    false)
  )
)
; --- 

;;; ----- Time

(declare-fun max_period () Int)
(assert (>= max_period 0))

;;; ----- The global policy 

; A "policy" is a sequence of conditional actions.
; A "slot" is a line number in this sequence.
; The two definitions below define a policy.

; maps (Nodes, Slots) to the action taken in this slot
(declare-fun GlobalPolicyAct (Node Int) Action)

; maps (Nodes, Slots) to the conditional under which the action in this slot is taken
(declare-fun GlobalPolicyCond (Node Int) Condition)

; --- information about slots
(declare-fun max_slots () Int)
(assert (>= max_slots 0))

;(declare-fun num_slots (Node) Int)
;(assert (forall ((x Node)) (>= (num_slots x) 0)))
;(define-fun num_slots ((x Node)) Int 5)

; --- always terminate with true condition
(assert (forall ((x Node)) (= (GlobalPolicyCond x max_slots) ctrue)))

; --- get the action for a node at the given time, starting at slot s, given the GlobalPolicy
(declare-fun get-action-for-time-slot (Node Int Int) Action)
(assert (forall ((x Node) (t Int) (s Int))
  (=>
    (and 
      (>= s 0) (<= s max_slots)
      (>= t 0) (< t max_period)
    )
    (= 
      (get-action-for-time-slot x t s)
      (let ((c (GlobalPolicyCond x s)))
      ; if s is the max slot for x, or the condition holds
      (ite (get-condition-holds c x t)
        ; if so, it is the conditional action
        (GlobalPolicyAct x s)
        ; otherwise, check the next slot
        (get-action-for-time-slot x t (+ s 1))
      ))
    )
  )
))
(define-fun get-action ((x Node) (t Int)) Action
  ; get the action, starting from slot 0
  (get-action-for-time-slot x t 0)
)
; --- 

;;; ----- Utilities for how actions update the state

; connected
(declare-fun connectivity (Node Node Int) Real)
(assert (forall ((x Node) (y Node) (t Int))
  (=>
    (and (>= t 0) (< t max_period))
    (= 
      (connectivity x y t)
      (ite (= x R)
        (ite (or (= y A) (= y B) (= y C)) 
          1.0
          0.0)
      (ite (or (= x A) (= x B) (= x C))
        (ite (= y D)
          1.0
          0.0)
      ;; (= x D)
        0.0))
    )
  )
))
(define-fun get-connected ((x Node) (y Node) (t Int)) Bool 
;; TODO: take into account connectivity as a probability
  (> (connectivity x y t) 0.0)
)

; was the action successful?
(define-fun get-act-success ((x Node) (t Int)) Bool
  (let ((x_act_at_t (get-action x t)))
  (ite ((_ is act_send) x_act_at_t)
    (and 
      ; must be connected to destination at that time
      (get-connected x (_dst x_act_at_t) t) 
      ; packet must have already been received by x
      (GlobalState_prcv x (_pck x_act_at_t) t)
    )
    true
  )
  )
)

; holds if x sends packet p to y at time t
(define-fun get-sends ((x Node) (y Node) (p Packet) (t Int)) Bool
  (let ((x_act_at_t (get-action x t)))
  (and
    (ite ((_ is act_send) x_act_at_t)
      ; packet must be p and destination must be y
      (and 
        (= (_dst x_act_at_t) y)
        (= (_pck x_act_at_t) p)
      )
      false
    )
    (get-act-success x t)
  ))
)

; get energy consumption
(define-fun get-energy ((x Node) (t Int)) Real
  (let ((x_act_at_t (get-action x t)))
  (ite ((_ is act_send) x_act_at_t)
    1.0
    0.05
  ))
)

;;; ----- Initial state

; R has all packets, no one else has any packet
(assert (forall ((x Node) (p Packet)) (= (GlobalState_prcv x p 0) (= x R))))
(assert (forall ((x Node)) (= (GlobalState_energy x 0) 0.0)))

;;; ----- Transition relation 

(assert 
(forall ((x Node) (t Int))
(=>
  (and (>= t 0) (< t max_period))
  (and
    (forall ((p Packet))
      (= 
        (GlobalState_prcv x p (+ t 1)) 
        (or 
          (GlobalState_prcv x p t)
          (exists ((y Node)) (get-sends y x p t)))
      )
    )
    (=
      (GlobalState_energy x (+ t 1))
      (+ (GlobalState_energy x t) (get-energy x t))
    )
  )
))
)

;;; ----- Validity of actions

; cannot use the same channel
(assert
(forall ((x Node) (y Node) (t Int))
  (let ((x_act_at_t (get-action x t)))
  (let ((y_act_at_t (get-action y t)))
  (=>
    (and (>= t 0) (< t max_period) (not (= x y)))
    (=>
      (and ((_ is act_send) x_act_at_t) ((_ is act_send) y_act_at_t))
      (not (= (_chn x_act_at_t) (_chn y_act_at_t)))
    )
  )))
))

; cannot send packets you don't have
(assert
(forall ((x Node) (t Int))
  (let ((x_act_at_t (get-action x t)))
  (=>
    (and (>= t 0) (< t max_period))
    (=>
      ((_ is act_send) x_act_at_t) 
      (GlobalState_prcv x (_pck x_act_at_t) t)
    )
  ))
))



;;; ----- Requirements

(assert (GlobalState_prcv D P1 max_period))
(assert (< (GlobalState_energy R max_period) 3.0))
(assert (< (GlobalState_energy A max_period) 3.0))
(assert (< (GlobalState_energy B max_period) 3.0))
(assert (< (GlobalState_energy C max_period) 3.0))
(assert (< (GlobalState_energy D max_period) 3.0))

(check-sat)

