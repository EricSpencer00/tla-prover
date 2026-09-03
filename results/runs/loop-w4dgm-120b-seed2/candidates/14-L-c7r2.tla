---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

(* Model-checking configuration for the Boulanger mutual exclusion algorithm.  *)
(* Overrides the NATURAL infinite set with a bounded range up to MaxNat, and   *)
(* adds a state constraint to keep ticket numbers inside that range.           *)

CONSTANTS N, MaxNat

VARIABLES token, want, inCS, ticket, pc

vars == <<token, want, inCS, ticket, pc>>

Processes == 1..N
MaxP == N

\* The overloaded operator name Nat is replaced by the finite version NatOverride
\* from the .cfg, so only this definition is needed and Nat itself must not be
\* declared or redefined here -- it comes from Naturals, which is still EXTENDED.
NatOverride(n) == 1 + n % MaxNat

Init ==
  /\ token = 1
  /\ want = [p \in Processes |-> FALSE]
  /\ inCS = [p \in Processes |-> FALSE]
  /\ ticket = [p \in Processes |-> 0]
  /\ pc = [p \in Processes |-> "idle"]

Request(p) ==
  /\ ~want[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ pc' = [pc EXCEPT ![p] = "requesting"]
  /\ UNCHANGED <<token, inCS, ticket>>

Acquire(p) ==
  /\ want[p]
  /\ ~inCS[p]
  /\ token = p
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = NatOverride(ticket[p])]
  /\ pc' = [pc EXCEPT ![p] = "critical"]
  /\ UNCHANGED <<token, want>>

Release(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ token' = NatOverride(token)
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED ticket

PassToken ==
  /\ \A p \in Processes : ~inCS[p]
  /\ token' = NatOverride(token)
  /\ UNCHANGED <<want, inCS, ticket, pc>>

Next ==
  \/ \E p \in Processes : Request(p) \/ Acquire(p) \/ Release(p)
  \/ PassToken

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ token \in 1..MaxNat
  /\ want \in [Processes -> BOOLEAN]
  /\ inCS \in [Processes -> BOOLEAN]
  /\ ticket \in [Processes -> 0..MaxNat]
  /\ pc \in [Processes -> {"idle", "requesting", "critical"}]

MutualExclusion ==
  \A p \in Processes : inCS[p] => token = p

(* The full inductive invariant from the Boulanger spec, carried over unchanged. *)
Inv ==
  /\ \A p \in Processes : inCS[p] => token = p
  /\ \A p \in Processes : (want[p] /\ ~inCS[p]) => token # p
  /\ \A p, q \in Processes : (inCS[p] /\ inCS[q]) => p = q

StateConstraint == \A p \in Processes : ticket[p] < MaxNat

====