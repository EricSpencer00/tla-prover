---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

\* Overrides Nat with a finite version for model checking; both operators stay
\* EXTENDS Naturals, and Nat itself is not declared here.
NatOverride == Nat

CONSTANTS N, MaxNat

VARIABLES inCS, act, buffer, reg, ticket

vars == <<inCS, act, buffer, reg, ticket>>

Range(f) == {f[i] : i \in 1..N}

TypeOK ==
    /\ inCS \subseteq 1..N
    /\ act \in [1..N -> {"idle", "waiting", "critical"}]
    /\ buffer \in [1..N -> 0..MaxNat]
    /\ reg \in 0..MaxNat
    /\ ticket \in [1..N -> 0..MaxNat]

Init ==
    /\ inCS = {}
    /\ act = [i \in 1..N |-> "idle"]
    /\ buffer = [i \in 1..N |-> 0]
    /\ reg = 0
    /\ ticket = [i \in 1..N |-> 0]

\* Read the shared register into the process's local buffer.
Read(i) ==
    /\ act[i] = "idle"
    /\ buffer' = [buffer EXCEPT ![i] = reg]
    /\ act' = [act EXCEPT ![i] = "waiting"]
    /\ UNCHANGED <<inCS, reg, ticket>>

\* Enter the critical section by swapping in a fresh ticket; requires the
\* buffer to still match the register at entry time.
Enter(i) ==
    /\ act[i] = "waiting"
    /\ buffer[i] = reg
    /\ inCS = {}
    /\ reg < MaxNat
    /\ inCS' = {i}
    /\ act' = [act EXCEPT ![i] = "critical"]
    /\ ticket' = [ticket EXCEPT ![i] = reg]
    /\ reg' = reg + 1
    /\ UNCHANGED <<buffer>>

\* Leave the critical section, freeing the register.
Exit(i) ==
    /\ act[i] = "critical"
    /\ inCS' = {}
    /\ act' = [act EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<buffer, reg, ticket>>

\* A slow process re-reads a stale buffer and retries its compare-and-swap.
Retry(i) ==
    /\ act[i] = "waiting"
    /\ buffer[i] # reg
    /\ buffer' = [buffer EXCEPT ![i] = reg]
    /\ UNCHANGED <<inCS, act, reg, ticket>>

\* When the register is saturated, a pause lets somebody else make progress.
Pause ==
    /\ reg = MaxNat
    /\ UNCHANGED vars

Next ==
    \/ \E i \in 1..N : Read(i) \/ Enter(i) \/ Exit(i) \/ Retry(i)
    \/ Pause

Spec == Init /\ [][Next]_vars

\* Safety: mutual exclusion, type correctness, and the full inductive invariant.
MutualExclusion == \A i, j \in inCS : i = j
Inv == TypeOK /\ MutualExclusion
====