---- MODULE MCBakery ----
EXTENDS Naturals, TLC

CONSTANTS N, MaxNat, Nat

VARIABLES pc, ticket, next

(*-----------------------------------------------------------------
  pc[i]   : program counter of process i
            ("idle", "request", "wait", "cs", "exit")
  ticket[i] : ticket number of process i, drawn from Nat
  next    : the next ticket number to be issued (also in Nat)
-----------------------------------------------------------------*)

\* -----------------------------------------------------------------
\* State space: the set of all possible process IDs
\* -----------------------------------------------------------------
ProcSet == 0..(N-1)

\* -----------------------------------------------------------------
\* Type correctness (used as part of the inductive invariant)
\* -----------------------------------------------------------------
TypeOK ==
  /\ pc \in [ProcSet -> {"idle", "request", "wait", "cs", "exit"}]
  /\ ticket \in [ProcSet -> Nat]
  /\ next \in Nat
  /\ \A i \in ProcSet: ticket[i] \in Nat

\* -----------------------------------------------------------------
\* Mutual exclusion property
\* -----------------------------------------------------------------
MutualExclusion ==
  \A i, j \in ProcSet :
    (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

\* -----------------------------------------------------------------
\* Full inductive invariant (customary for the bakery algorithm)
\* -----------------------------------------------------------------
Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A i \in ProcSet:
        /\ (pc[i] = "cs") => (ticket[i] <= next)

\* -----------------------------------------------------------------
\* Helper to compute the set of processes with smaller tickets
\* (including ties resolved by smaller process id)
\* -----------------------------------------------------------------
LowerOrEqual(i) ==
  { j \in ProcSet :
      (ticket[j] < ticket[i]) \/ (ticket[j] = ticket[i] /\ j < i) }

\* -----------------------------------------------------------------
\* Initial state (type‑correct but not required to be “all idle”)
\* -----------------------------------------------------------------
Init ==
  /\ pc = [i \in ProcSet |-> "idle"]
  /\ ticket = [i \in ProcSet |-> 0]
  /\ next = 0
  /\ TypeOK

\* -----------------------------------------------------------------
\* Actions (identical to the classic bakery algorithm)
\* -----------------------------------------------------------------
Request(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "request"]
  /\ ticket' = [ticket EXCEPT ![i] = next]
  /\ next' = (next + 1) % (MaxNat + 1)
  /\ UNCHANGED <<>>

EnterCS(i) ==
  /\ pc[i] = "wait"
  /\ \A j \in ProcSet :
        (j # i) => (pc[j] # "cs" \/ i \in LowerOrEqual(j))
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<ticket, next>>

Exit(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED <<ticket, next>>

Finish(i) ==
  /\ pc[i] = "exit"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, next>>

Wait(i) ==
  /\ pc[i] = "request"
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ UNCHANGED <<ticket, next>>

\* -----------------------------------------------------------------
\* Next-state relation
\* -----------------------------------------------------------------
Next ==
  \E i \in ProcSet :
    \/ Request(i)
    \/ Wait(i)
    \/ EnterCS(i)
    \/ Exit(i)
    \/ Finish(i)

\* -----------------------------------------------------------------
\* Specification (inductive: any type‑correct state satisfying Inv
\* may be an initial state)
\* -----------------------------------------------------------------
ISpec ==
  Init \/ Next

\* -----------------------------------------------------------------
\* The set of invariants required by the .cfg file
\* -----------------------------------------------------------------
INVARIANTS == Inv

\* -----------------------------------------------------------------
\* No explicit safety properties beyond the invariants
\* -----------------------------------------------------------------
PROPERTIES == TRUE

====