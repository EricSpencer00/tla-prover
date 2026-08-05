---- MODULE MCBoulanger ----
\* Boulanger's Bakery shop: a bakery takes orders and serves them, and a
\* bounded-stock, bounded-service-semantics is expected -- the shop's ovens
\* and counters can only hold so much at once. The number of customers in
\* service at a moment must never exceed the shop's capacity.
EXTENDS Naturals

NONE == "none"
Procs == {"w1", "w2"}
MaxNat == 2

VARIABLES pc, num
vars == <<pc, num>>

TypeOK ==
  /\ pc \in [Procs -> {"idle", "wating", "paying"}]
  /\ num \in 0 .. MaxNat

Init ==
  /\ pc = [p \in Procs |-> "idle"]
  /\ num = 0

\* A waiting customer orders a loaf, only if the shop has room for another
\* order now in service.
Request(p) ==
  /\ pc[p] = "idle"
  /\ num < MaxNat
  /\ pc' = [pc EXCEPT ![p] = "wating"]
  /\ num' = (num) + 1

\* The shop begins preparing the order.
Prepare(p) ==
  /\ pc[p] = "wating"
  /\ pc' = [pc EXCEPT ![p] = "paying"]
  /\ UNCHANGED num

\* The order is handed over; the customer leaves, freeing room.
Serve(p) ==
  /\ pc[p] = "paying"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ num' = (num) - 1

Next ==
  \/ \E p \in Procs : Request(p)
  \/ \E p \in Procs : Prepare(p)
  \/ \E p \in Procs : Serve(p)

Spec == Init /\ [][Next]_vars

\* The shop never has more customers in service than it can hold at once.
BoundedService == num <= MaxNat

====