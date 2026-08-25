---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

(*--- finite replacement for the infinite set Nat ---*)
NatOverride == 0..MaxNat

Proc == 1..N

VARIABLES choosing, number, cs

vars == <<choosing, number, cs>>

(*--- initial state ---*)
Init ==
    /\ choosing = [i \in Proc |-> FALSE]
    /\ number   = [i \in Proc |-> 0]
    /\ cs       = {}

(*--- type correctness invariant ---*)
TypeOK ==
    /\ choosing \in [Proc -> BOOLEAN]
    /\ number   \in [Proc -> NatOverride]
    /\ cs       \subseteq Proc
    /\ \A i \in Proc : i \in cs => number[i] # 0

(*--- mutual exclusion invariant ---*)
MutualExclusion ==
    /\ \A i, j \in cs : i = j

(*--- full inductive invariant ---*)
Inv == TypeOK /\ MutualExclusion

(*--- actions of the Bakery algorithm ---*)

Request(i) ==
    /\ i \in Proc
    /\ ~choosing[i]
    /\ number[i] = 0
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<number, cs>>

Assign(i) ==
    /\ i \in Proc
    /\ choosing[i] = TRUE
    /\ number[i] = 0
    /\ number' = [number EXCEPT ![i] = (Max({ number[j] : j \in Proc }) + 1) % (MaxNat + 1)]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ UNCHANGED cs

Enter(i) ==
    /\ i \in Proc
    /\ number[i] # 0
    /\ \A j \in Proc :
          (j # i) => ( number[j] = 0
                       \/ number[j] > number[i]
                       \/ (number[j] = number[i] /\ i < j) )
    /\ cs' = cs \cup {i}
    /\ UNCHANGED <<choosing, number>>

Exit(i) ==
    /\ i \in Proc
    /\ i \in cs
    /\ cs' = cs \ {i}
    /\ number' = [number EXCEPT ![i] = 0]
    /\ UNCHANGED <<choosing, cs>>

Next ==
    \/ \E i \in Proc : Request(i)
    \/ \E i \in Proc : Assign(i)
    \/ \E i \in Proc : Enter(i)
    \/ \E i \in Proc : Exit(i)

(*--- inductive specification (starts from any type‑correct state) ---*)
ISpec ==
    (Init \/ Inv) /\ [][Next]_vars

====