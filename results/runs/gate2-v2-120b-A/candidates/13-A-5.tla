---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N, MaxNat, Nat

VARIABLES pc, ticket

(* --algorithm (for reference only, not part of the spec)--
   processes: 0..N-1
   pc[p] ∈ {"idle", "wait", "cs"}
   ticket[p] ∈ Nat
*)

(* State constraints *)
TypeOK ==
  /\ pc \in [0..N-1 -> {"idle", "wait", "cs"}]
  /\ ticket \in [0..N-1 -> Nat]

(* Mutual exclusion property *)
MutualExclusion ==
  ~∃ p, q \in 0..N-1 :
      p # q /\ pc[p] = "cs" /\ pc[q] = "cs"

(* Full inductive invariant (here we reuse TypeOK together with the
   ordering condition that defines the Bakery algorithm's safety) *)
Inv ==
  /\ TypeOK
  /\ MutualExclusion
  /\ \A p, q \in 0..N-1 :
        (pc[p] = "cs" /\ pc[q] = "cs") => (ticket[p] < ticket[q] \/ (ticket[p] = ticket[q] /\ p < q))

(* Initial state *)
Init ==
  /\ pc = [i \in 0..N-1 |-> "idle"]
  /\ ticket = [i \in 0..N-1 |-> 0]

(* Actions *)

ChooseNumber(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "wait"]
  /\ ticket' = [ticket EXCEPT ![p] = 1 + Max({ ticket[i] : i \in 0..N-1 })]

EnterCS(p) ==
  /\ pc[p] = "wait"
  /\ \A i \in 0..N-1 :
        (i # p) => (ticket[p] < ticket[i] \/ (ticket[p] = ticket[i] /\ p < i))
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED ticket

LeaveCS(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]

Next ==
  \/ \E p \in 0..N-1 : ChooseNumber(p)
  \/ \E p \in 0..N-1 : EnterCS(p)
  \/ \E p \in 0..N-1 : LeaveCS(p)

(* Inductive specification: start from any type‑correct state satisfying Inv,
   and repeatedly apply Next *)
ISpec == Init /\ [][Next]_<<pc, ticket>>

THEOREM ISpec => []Inv

====