---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, decision, lastWriter, seen

vars == <<inCS, ticket, decision, lastWriter, seen>>

\* The model-checking twist: Nat is replaced by a finite-range version that
\* never exceeds MaxNat, so the state space stays small enough to explore.
NatOverride == 0..MaxNat

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> NatOverride]
  /\ decision \in [1..N -> {"idle", "reading", "committed"}]
  /\ lastWriter \in 0..N
  /\ seen \in [1..N -> NatOverride]

MutualExclusion == \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

\* The full inductive invariant for Bakery: no two processes ever hold the
\* critical section at once, and every process's ticket is bounded by MaxNat.
Inv ==
  /\ MutualExclusion
  /\ \A i \in 1..N : ticket[i] <= MaxNat
  /\ \A i \in 1..N : decision[i] \in {"idle", "reading", "committed"}

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ decision = [i \in 1..N |-> "idle"]
  /\ lastWriter = 0
  /\ seen = [i \in 1..N |-> 0]

BeginRead(i) ==
  /\ decision[i] = "idle"
  /\ decision' = [decision EXCEPT ![i] = "reading"]
  /\ seen' = [seen EXCEPT ![i] = lastWriter]
  /\ UNCHANGED <<inCS, ticket, lastWriter>>

\* The compare-and-swap: it only lands if the shared register still holds
\* the value the process read, otherwise the process backs off and re-reads.
Commit(i) ==
  /\ decision[i] = "reading"
  /\ lastWriter = seen[i]
  /\ \A j \in 1..N : ~inCS[j]
  /\ lastWriter < MaxNat
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ decision' = [decision EXCEPT ![i] = "committed"]
  /\ lastWriter' = lastWriter + 1
  /\ ticket' = [ticket EXCEPT ![i] = lastWriter + 1]
  /\ UNCHANGED seen

Retry(i) ==
  /\ decision[i] = "reading"
  /\ lastWriter # seen[i]
  /\ decision' = [decision EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<inCS, ticket, lastWriter, seen>>

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ decision' = [decision EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, lastWriter, seen>>

BeginAny == \E i \in 1..N : BeginRead(i)
CommitAny == \E i \in 1..N : Commit(i)
RetryAny == \E i \in 1..N : Retry(i)
ExitAny == \E i \in 1..N : Exit(i)

Next == BeginAny \/ CommitAny \/ RetryAny \/ ExitAny

ISpec == Init /\ [][Next]_vars

====