---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, MaxNat, Nat

VARIABLES ns, ds, pc

(*--------------------------------------------------------------
  Types
----------------------------------------------------------------*)
TypeOK ==
  /\ ns \in [0..N-1 -> Nat]
  /\ ds \in [0..N-1 -> Nat]
  /\ pc \in [0..N-1 -> {"idle", "waiting", "cs"}]

(*--------------------------------------------------------------
  Initial predicate (any type-correct state)
----------------------------------------------------------------*)
Init ==
  /\ TypeOK
  /\ \A i \in 0..N-1: pc[i] = "idle"

(*--------------------------------------------------------------
  Actions
----------------------------------------------------------------*)
SetTicket(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "waiting"]
  /\ ns' = [ns EXCEPT ![i] = Max(ds) + 1]
  /\ ds' = ds

Enter(i) ==
  /\ pc[i] = "waiting"
  /\ \A j \in 0..N-1 :
        (pc[j] # "cs") \/ (j # i /\ ns[i] > ns[j]) \/ (j # i /\ ns[i] = ns[j] /\ i > j)
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<ns, ds>>

Exit(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ ds' = [ds EXCEPT ![i] = MaxNat]
  /\ UNCHANGED ns

Next ==
  \/ \E i \in 0..N-1: SetTicket(i)
  \/ \E i \in 0..N-1: Enter(i)
  \/ \E i \in 0..N-1: Exit(i)

(*--------------------------------------------------------------
  Safety invariants
----------------------------------------------------------------*)
MutualExclusion ==
  \A i, j \in 0..N-1 :
    (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Inv ==
  /\ TypeOK
  /\ MutualExclusion

(*--------------------------------------------------------------
  Specification
----------------------------------------------------------------*)
ISpec == Init /\ [][Next]_<<ns, ds, pc>>

====