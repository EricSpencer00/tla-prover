---- MODULE W4Od15m6p5t4 ----
EXTENDS Naturals, FiniteSets

(* A stock exchange opening auction executes match orders.  Executing an order is *)
(* irreversible and must happen at most once per order.  A single lease with       *)
(* expiry serialises the matcher: only the holder of an unexpired lease may         *)
(* execute, and only while the number of executed orders is below the auction       *)
(* capacity, which changes at runtime.                                             *)

CONSTANTS MaxT, TTL, MaxOrders

Orders  == {"o1", "o2"}
Matchers == {"m1", "m2"}
NoOne   == "none"

VARIABLES clock, holder, expiry, executed, capacity

vars == << clock, holder, expiry, executed, capacity >>

ExecutedOrders == {o \in Orders : executed[o] >= 1}

TypeOK ==
    /\ clock \in 0..MaxT
    /\ holder \in Matchers \cup {NoOne}
    /\ expiry \in 0..MaxT
    /\ executed \in [Orders -> Nat]
    /\ capacity \in 1..MaxOrders

Init ==
    /\ clock = 0
    /\ holder = NoOne
    /\ expiry = 0
    /\ executed = [o \in Orders |-> 0]
    /\ capacity = MaxOrders

Tick ==
    /\ clock < MaxT
    /\ clock' = clock + 1
    /\ UNCHANGED << holder, expiry, executed, capacity >>

Acquire(m) ==
    /\ (holder = NoOne \/ clock >= expiry)
    /\ holder' = m
    /\ expiry' = IF clock + TTL <= MaxT THEN clock + TTL ELSE MaxT
    /\ UNCHANGED << clock, executed, capacity >>

Release(m) ==
    /\ holder = m
    /\ holder' = NoOne
    /\ UNCHANGED << clock, expiry, executed, capacity >>

\* Irreversibly execute an order; requires a valid lease and room under capacity.
Execute(m, o) ==
    /\ holder = m
    /\ clock < expiry
    /\ executed[o] = 0
    /\ Cardinality(ExecutedOrders) < capacity
    /\ executed' = [executed EXCEPT ![o] = @ + 1]
    /\ UNCHANGED << clock, holder, expiry, capacity >>

\* The auction capacity is re-provisioned at runtime.
Resize(k) ==
    /\ k # capacity
    /\ capacity' = k
    /\ UNCHANGED << clock, holder, expiry, executed >>

Next ==
    \/ Tick
    \/ \E m \in Matchers : Acquire(m)
    \/ \E m \in Matchers : Release(m)
    \/ \E m \in Matchers, o \in Orders : Execute(m, o)
    \/ \E k \in 1..MaxOrders : Resize(k)

Spec == Init /\ [][Next]_vars

(* The irreversible execution happens at most once per order.                   *)
ExecuteAtMostOnce == \A o \in Orders : executed[o] <= 1
====