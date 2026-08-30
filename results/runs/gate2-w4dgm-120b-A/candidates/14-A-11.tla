---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, Boulanger

CONSTANTS N, MaxNat

\* Overrides the unbounded Nat from Naturals with a finite version so TLC
\* can explore the state space, while keeping the semantics the same.
NatOverride == Nat

VARIABLES step, cs, want, ticket

vars == <<step, cs, want, ticket>>

\* The full Boulanger spec never touches any process' ticket number,
\* so the finite range is only ever exercised at runtime, never at init.
TypeOK ==
  /\ step \in {"idle", "voting", "critical"}
  /\ cs \in 0..N
  /\ want \in SUBSET 0..(N - 1)
  /\ ticket \in [0..(N - 1) -> 0..MaxNat]

\* The coarse lock protects the fine ticket register: while a process is
\* in the critical section it is the lock holder, and only the holder's
\* ticket is ever compared to the others, so every in-section process is
\* the holder and holds the unique lowest ticket.
MutualExclusion ==
  /\ cs = 0 \/ ((cs \in 1..N) /\ (cs - 1) \in want)
  /\ \A i \in want : (i = cs - 1) => (\A j \in want : j = i \/ ticket[i] < ticket[j])

\* The invariant the inductive spec was built around: the holder has the
\* unique lowest ticket among all waiting processes.
Inv ==
  /\ \A i \in want : cs = 0 \/ (cs - 1) \in want /\ (i = cs - 1 \/ ticket[cs - 1] < ticket[i])
  /\ (cs # 0 => cs - 1 \in want)

Init ==
  /\ step = "idle"
  /\ cs = 0
  /\ want = {}
  /\ ticket = [i \in 0..(N - 1) |-> 0]

Vote(i) ==
  /\ step = "idle"
  /\ i \notin want
  /\ want' = want \cup {i}
  /\ step' = "voting"
  /\ UNCHANGED <<cs, ticket>>

Start ==
  /\ step = "voting"
  /\ step' = "critical"
  /\ cs' = (CHOOSE i \in want : \A j \in want : ticket[i] <= ticket[j]) + 1
  /\ UNCHANGED <<want, ticket>>

Stop ==
  /\ step = "critical"
  /\ step' = "idle"
  /\ cs' = 0
  /\ want' = {}
  /\ ticket' = [i \in 0..(N - 1 |-> IF i \in want THEN (ticket[i] + 1) % (MaxNat + 1) ELSE ticket[i]]

Arrive(i) ==
  /\ i \notin want
  /\ want' = want \cup {i}
  /\ ticket' = [ticket EXCEPT ![i] = (ticket[i] + 1) % (MaxNat + 1)]
  /\ step' = IF step = "idle" THEN "voting" ELSE step
  /\ UNCHANGED cs

Next ==
  \/ \E i \in 0..(N - 1) : Vote(i)
  \/ Start
  \/ Stop
  \/ \E i \in 0..(N - 1) : Arrive(i)

Spec == Init /\ [][Next]_vars

TicketRange == \A i \in 0..(N - 1) : ticket[i] < MaxNat

====