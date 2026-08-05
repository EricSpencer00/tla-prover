---- MODULE MCBakery ----
EXTENDS Bakery

(* A bakery with a bounded number of customers, each latch in the bakery's
   interior being modeled as a bounded FIFO queue: a customer requests entry,
   gets placed in the queue up to capacity, and is finally admitted.  The
   bounded capacity here is a runtime limit, not a runtime failure.  An
   operator can re-provision the number of active queues up to the model's
   compile-time configured ceiling MaxNat; re-provisioning can only be done
   while the bakery queue is empty, so it never moves customers out from
   under an already booked entry.  The bakery never loses a customer's
   request: every request is either waiting in the queue or admitted, never
   both, never neither. *)

CONSTANT MaxNat

ASSUME MaxNat \notin Nat

VARIABLES admitted, queue, maxSlots
vars == <<admitted, queue, maxSlots>>

Init ==
    /\ admitted = 0
    /\ queue = 0
    /\ maxSlots = 1

RequestEntry ==
    /\ queue < maxSlots
    /\ queue' = queue + 1
    /\ UNCHANGED <<admitted, maxSlots>>

Admit ==
    /\ queue > 0
    /\ queue' = queue - 1
    /\ admitted' = admitted + 1
    /\ UNCHANGED maxSlots

Reprovision ==
    /\ queue = 0
    /\ maxSlots < MaxNat
    /\ maxSlots' = maxSlots + 1
    /\ UNCHANGED <<admitted, queue>>

Next == RequestEntry \/ Admit \/ Reprovision

Spec == Init /\ [][Next]_vars

(* Liveness: a waiting customer is eventually admitted. *)
QueueDrains == (queue > 0) ~> (queue = 0)

====