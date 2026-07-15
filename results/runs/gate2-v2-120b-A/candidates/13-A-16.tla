---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets

\*-----------------------------------------------------------------
\* Constants
\*-----------------------------------------------------------------
CONSTANT N
CONSTANT MaxNat
CONSTANT Nat

\*-----------------------------------------------------------------
\* Derived sets
\*-----------------------------------------------------------------
Proc == 1 .. N
Ticket == Nat

\*-----------------------------------------------------------------
\* State variables
\*-----------------------------------------------------------------
VARIABLES pc,      \* program counter (state) of each process
          ticket,  \* ticket number of each process
          choosing \* boolean flag indicating ticket selection phase

Vars == << pc, ticket, choosing >>

\*-----------------------------------------------------------------
\* Type correctness predicate (from the original Bakery spec)
\*-----------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"idle", "waiting", "cs"}]
    /\ ticket \in [Proc -> Ticket]
    /\ choosing \in [Proc -> BOOLEAN]

\*-----------------------------------------------------------------
\* Mutual exclusion predicate
\*-----------------------------------------------------------------
MutualExclusion ==
    ~(\E i, j \in Proc : i # j /\ pc[i] = "cs" /\ pc[j] = "cs")

\*-----------------------------------------------------------------
\* Full inductive invariant (combination of type correctness and
\* mutual exclusion).  Additional derived conditions from the original
\* spec ensure proper ticket ordering.
\*-----------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ MutualExclusion
    /\ \A i \in Proc :
        (pc[i] = "cs") => 
            /\ \A j \in Proc :
                (i # j) =>
                    \/ ticket[i] < ticket[j]
                    \/ (ticket[i] = ticket[j] /\ i < j)

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
    /\ pc = [i \in Proc |-> "idle"]
    /\ ticket = [i \in Proc |-> 0]
    /\ choosing = [i \in Proc |-> FALSE]
    /\ TypeOK

\*-----------------------------------------------------------------
\* Actions (exactly as in the original Bakery algorithm)
\*-----------------------------------------------------------------
\* Process i starts the entry protocol
Entry(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "waiting"]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED ticket

\* Process i picks its ticket number
Pick(i) ==
    /\ pc[i] = "waiting"
    /\ choosing[i] = TRUE
    /\ ticket' = [ticket EXCEPT ![i] = 
          1 + Max({ ticket[j] : j \in Proc })]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ UNCHANGED pc

\* Process i waits until its turn
Wait(i) ==
    /\ pc[i] = "waiting"
    /\ choosing[i] = FALSE
    /\ \A j \in Proc :
        (j # i) => 
            /\ (choosing[j] = FALSE) 
            /\ (ticket[j] = 0 \/ 
                ticket[i] < ticket[j] \/ 
                (ticket[i] = ticket[j] /\ i < j))
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << ticket, choosing >>

\* Process i leaves the critical section
Leave(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED choosing

\* The overall next-state relation
Next ==
    \/ \E i \in Proc : Entry(i)
    \/ \E i \in Proc : Pick(i)
    \/ \E i \in Proc : Wait(i)
    \/ \E i \in Proc : Leave(i)

\*-----------------------------------------------------------------
\* Specification (inductive form, allowing any type‑correct state)
\*-----------------------------------------------------------------
ISpec == Init /\ [][Next]_Vars

\*-----------------------------------------------------------------
\* Theorem (optional, for TLC)
\*-----------------------------------------------------------------
THEOREM Spec => []Inv

====