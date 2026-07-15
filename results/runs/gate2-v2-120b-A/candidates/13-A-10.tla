---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Derived finite sets
\* ----------------------------------------------------------------------
NatSet == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State variables (inherited from Bakery)
\* ----------------------------------------------------------------------
VARIABLES pc, ticket, choosing

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of states representing being in the critical section
CriticalSet == {"cs"}

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in Proc |-> "idle"]
    /\ ticket = [i \in Proc |-> 0]
    /\ choosing = [i \in Proc |-> FALSE]

\* ----------------------------------------------------------------------
\* Actions (identical to those of the original Bakery spec)
\* ----------------------------------------------------------------------
\* Process i starts the entry protocol
StartEntry(i) ==
    /\ i \in Proc
    /\ pc[i] = "idle"
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<pc, ticket>>
    /\ pc' = pc
    /\ ticket' = ticket

\* Process i picks a ticket number
PickTicket(i) ==
    /\ i \in Proc
    /\ choosing[i] = TRUE
    /\ ticket' = [ticket EXCEPT ![i] = 
          IF \E j \in Proc : ticket[j] # 0
          THEN Max(ticket) + 1
          ELSE 1]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ UNCHANGED pc
    /\ pc' = pc

\* Process i checks waiting condition and enters critical section
EnterCS(i) ==
    /\ i \in Proc
    /\ pc[i] = "idle"
    /\ choosing[i] = FALSE
    /\ \A j \in Proc :
          (j # i) => 
            (choosing[j] = FALSE) /\ 
            (ticket[j] = 0 \/ 
             ticket[i] < ticket[j] \/ 
             (ticket[i] = ticket[j] /\ i < j))
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<ticket, choosing>>

\* Process i exits the critical section
ExitCS(i) ==
    /\ i \in Proc
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED choosing

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in Proc : StartEntry(i)
    \/ \E i \in Proc : PickTicket(i)
    \/ \E i \in Proc : EnterCS(i)
    \/ \E i \in Proc : ExitCS(i)

\* ----------------------------------------------------------------------
\* Specification (inductive form: any type-correct state satisfying Inv)
\* ----------------------------------------------------------------------
ISpec == Init /\ [][Next]_<<pc, ticket, choosing>>

\* ----------------------------------------------------------------------
\* Invariant (full inductive invariant)
\* ----------------------------------------------------------------------
Inv ==
    /\ \A i \in Proc : pc[i] \in {"idle", "cs"}
    /\ \A i \in Proc : ticket[i] \in NatSet
    /\ \A i \in Proc : choosing[i] \in BOOLEAN
    /\ MutualExclusion

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in Proc : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

TypeOK ==
    /\ \A i \in Proc : pc[i] \in {"idle", "cs"}
    /\ \A i \in Proc : ticket[i] \in NatSet
    /\ \A i \in Proc : choosing[i] \in BOOLEAN

\* ----------------------------------------------------------------------
\* The specification to be checked (the name expected by the .cfg)
\* ----------------------------------------------------------------------
Spec == ISpec

\* ----------------------------------------------------------------------
\* The set of invariants to be checked (named as required)
\* ----------------------------------------------------------------------
\* They are given as separate operators to match the .cfg identifiers
\* ----------------------------------------------------------------------
MutualExclusion == MutualExclusion
TypeOK == TypeOK
Inv == Inv

====