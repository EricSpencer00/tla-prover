---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

\*-----------------------------------------------------------------
\* Constants required by the configuration
\*-----------------------------------------------------------------
CONSTANT N
CONSTANT MaxNat

\*-----------------------------------------------------------------
\* Finite version of Nat for model checking
\*-----------------------------------------------------------------
NatOverride == 0 .. MaxNat

\*-----------------------------------------------------------------
\* Derived sets
\*-----------------------------------------------------------------
Proc == 1 .. N

\*-----------------------------------------------------------------
\* State variables (same as in the Bakery specification)
\*-----------------------------------------------------------------
VARIABLES choosing, number, cs

\*-----------------------------------------------------------------
\* Type correctness predicate
\*-----------------------------------------------------------------
TypeOK ==
    /\ N \in Nat
    /\ MaxNat \in Nat
    /\ choosing \in [Proc -> BOOLEAN]
    /\ number   \in [Proc -> NatOverride]
    /\ cs       \in [Proc -> BOOLEAN]

\*-----------------------------------------------------------------
\* Mutual exclusion predicate
\*-----------------------------------------------------------------
MutualExclusion ==
    \A i, j \in Proc :
        (cs[i] /\ cs[j]) => i = j

\*-----------------------------------------------------------------
\* Full inductive invariant (as required by the .cfg)
\*-----------------------------------------------------------------
Inv == TypeOK /\ MutualExclusion

\*-----------------------------------------------------------------
\* Initial state (identical to the original Bakery spec, but with
\* numbers confined to NatOverride)
\*-----------------------------------------------------------------
Init ==
    /\ choosing = [i \in Proc |-> FALSE]
    /\ number   = [i \in Proc |-> 0]
    /\ cs       = [i \in Proc |-> FALSE]

\*-----------------------------------------------------------------
\* Helper definition: maximum ticket currently in use
\*-----------------------------------------------------------------
MaxTicket ==
    IF {} = {} THEN 0
    ELSE Max({ number[j] : j \in Proc })

\*-----------------------------------------------------------------
\* Actions for a single process i
\*-----------------------------------------------------------------
StartChoosing(i) ==
    /\ i \in Proc
    /\ ¬choosing[i]
    /\ number[i] = 0
    /\ cs[i] = FALSE
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<number, cs>>

AssignNumber(i) ==
    /\ i \in Proc
    /\ choosing[i] = TRUE
    /\ number' = [number EXCEPT ![i] = (MaxTicket + 1) % (MaxNat + 1)]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ UNCHANGED cs
    /\ number'[i] \in NatOverride

EnterCS(i) ==
    /\ i \in Proc
    /\ ¬cs[i]
    /\ number[i] # 0
    /\ \A j \in Proc :
         (j # i) => ( number[j] = 0
                     \/ number[j] > number[i]
                     \/ (number[j] = number[i] /\ j > i) )
    /\ cs' = [cs EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<choosing, number>>

ExitCS(i) ==
    /\ i \in Proc
    /\ cs[i] = TRUE
    /\ cs' = [cs EXCEPT ![i] = FALSE]
    /\ number' = [number EXCEPT ![i] = 0]
    /\ UNCHANGED choosing

\*-----------------------------------------------------------------
\* The Next-state relation (any process may take any enabled step)
\*-----------------------------------------------------------------
Next ==
    \/ \E i \in Proc : StartChoosing(i)
    \/ \E i \in Proc : AssignNumber(i)
    \/ \E i \in Proc : EnterCS(i)
    \/ \E i \in Proc : ExitCS(i)
    \/ UNCHANGED <<choosing, number, cs>>

\*-----------------------------------------------------------------
\* Specification used by TLC (inductive specification)
\*-----------------------------------------------------------------
Vars == <<choosing, number, cs>>
ISpec == Init /\ [][Next]_Vars

====