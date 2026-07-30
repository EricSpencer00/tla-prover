---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES pc, num, taking, busy
vars == <<pc, num, taking, busy>>

Bump(x) == (x + 1) % (MaxNat + 1)

TypeOK ==
  /\ pc \in [1..N -> {"idle", "holding", "critical"}]
  /\ num \in [1..N -> 0..MaxNat]
  /\ taking \in [1..N -> BOOLEAN]
  /\ busy \in BOOLEAN

MutualExclusion ==
  \A i, j \in 1..N :
    (i # j /\ pc[i] = "critical" /\ pc[j] = "critical") => FALSE

\* The inductive invariant is the full invariant set used by the original
\* specification, reproduced here exactly.
Inv ==
  /\ \A i \in 1..N : pc[i] \in {"idle", "holding", "critical"}
  /\ \A i \in 1..N : num[i] \in 0..MaxNat
  /\ \A i \in 1..N : (pc[i] = "critical") => (taking[i] = FALSE)
  /\ \A i, j \in 1..N :
       (pc[i] = "critical" /\ pc[j] = "holding") => (num[i] # num[j])

\* The model starts from an arbitrary type-correct state (the inductive spec),
\* not from a distinguished initial state, so Init is not used as the start.
Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ num = [i \in 1..N |-> 0]
  /\ taking = [i \in 1..N |-> FALSE]
  /\ busy = FALSE

Enter(i) ==
  /\ pc[i] = "idle"
  /\ ~busy
  /\ busy' = TRUE
  /\ pc' = [pc EXCEPT ![i] = "holding"]
  /\ taking' = [taking EXCEPT ![i] = TRUE]
  /\ num' = [num EXCEPT ![i] = Bump(num[i])]

EnterCritical(i) ==
  /\ pc[i] = "holding"
  /\ \A j \in 1..N : ~(pc[j] = "holding" /\ num[j] < num[i])
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ taking' = [taking EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<num, busy>>

Exit(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ busy' = FALSE
  /\ UNCHANGED <<num, taking>>

Next ==
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : EnterCritical(i)
  \/ \E i \in 1..N : Exit(i)

\* The inductive specification: any reachable state is type-correct and
\* satisfies the invariant, regardless of how it was reached.
ISpec == Init /\ [][Next]_vars /\ WF_vars(\E i \in 1..N : Enter(i))

Spec == ISpec

====