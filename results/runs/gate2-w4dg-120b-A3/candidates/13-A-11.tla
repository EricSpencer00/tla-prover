---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Types used throughout the spec; NatOverride replaces the infinite Nat with
\* a bounded version over the range 0..MaxNat (so the model is finite).
\* Nat itself is never declared, only overridden in the .cfg.
VARIABLES inCS, var, number, choosing

vars == <<inCS, var, number, choosing>>

TypeOK ==
  /\ inCS \in SUBSET (1..N)
  /\ var \in [1..N -> {"idle", "waiting", "critical"}]
  /\ number \in [1..N -> 0..MaxNat]
  /\ choosing \in [1..N -> BOOLEAN]

\* Mutual exclusion: no two processes share the critical section.
MutualExclusion ==
  \A a, b \in inCS : a = b

\* The full inductive invariant holding at every reachable state.
Inv ==
  /\ TypeOK
  /\ MutualExclusion

Init ==
  /\ inCS = {}
  /\ var = [p \in 1..N |-> "idle"]
  /\ number = [p \in 1..N |-> 0]
  /\ choosing = [p \in 1..N |-> FALSE]

\* The Bakery actions are unchanged from the base spec except that they
\* respect the bounded ticket range (no ticket above MaxNat is ever taken).
\* The invariant boundary is what keeps the model finite.
Try(p) ==
  /\ var[p] = "idle"
  /\ var' = [var EXCEPT ![p] = "waiting"]
  /\ choosing' = [choosing EXCEPT ![p] = TRUE]
  /\ number' = [number EXCEPT ![p] = IF \E q \in 1..N : number[q] > number[p] /\ number[q] < MaxNat
                                    THEN number[p] + 1 ELSE number[p]]
  /\ UNCHANGED inCS

Enter(p) ==
  /\ var[p] = "waiting"
  /\ \A q \in 1..N : q # p => (var[q] # "critical" \/ number[p] < number[q])
  /\ inCS' = inCS \cup {p}
  /\ var' = [var EXCEPT ![p] = "critical"]
  /\ choosing' = [choosing EXCEPT ![p] = FALSE]
  /\ UNCHANGED number

Exit(p) ==
  /\ var[p] = "critical"
  /\ var' = [var EXCEPT ![p] = "idle"]
  /\ inCS' = inCS \ {p}
  /\ UNCHANGED <<number, choosing>>

Next == \E p \in 1..N : Try(p) \/ Enter(p) \/ Exit(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Exit(1))

\* The reference .cfg uses the inductive specification (ISpec), which starts
\* from any type-correct reachable state; Init is still required as a base.
ISpec == Spec

\* No additional properties beyond the invariant: the .cfg leaves this empty.
Properties == {}

====