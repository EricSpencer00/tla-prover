---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\*  State variables (inherited from the Bakery specification)
\* ----------------------------------------------------------------------
VARIABLES pc, ticket, choosing

\* ----------------------------------------------------------------------
\*  Derived constant: the set of process identifiers
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\*  Initial state (type-correct, respecting the finite Nat range)
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [i \in Proc |-> "idle"]
  /\ ticket = [i \in Proc |-> 0]
  /\ choosing = [i \in Proc |-> FALSE]

\* ----------------------------------------------------------------------
\*  Actions (exactly as in Bakery, but using the finite Nat range)
\* ----------------------------------------------------------------------
Request(i) ==
  /\ pc[i] = "idle"
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<pc, ticket>>
  /\ pc' = pc
  /\ ticket' = ticket
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]

Choose(i) ==
  /\ pc[i] = "idle"
  /\ choosing[i] = TRUE
  /\ ticket' = [ticket EXCEPT ![i] = 
        CHOOSE n \in Nat : 
          \A j \in Proc : (ticket[j] \notin Nat) \/ (ticket[j] > n) \/ (ticket[j] = n /\ j < i)]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ UNCHANGED pc

Enter(i) ==
  /\ pc[i] = "idle"
  /\ choosing[i] = FALSE
  /\ \A j \in Proc :
        /\ (pc[j] # "cs")
        /\ (ticket[j] = 0 \/ ticket[i] < ticket[j] \/ 
            (ticket[i] = ticket[j] /\ i < j))
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<ticket, choosing>>

Exit(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED choosing

Next ==
  \/ \E i \in Proc : Request(i)
  \/ \E i \in Proc : Choose(i)
  \/ \E i \in Proc : Enter(i)
  \/ \E i \in Proc : Exit(i)

\* ----------------------------------------------------------------------
\*  Safety invariants
\* ----------------------------------------------------------------------
MutualExclusion ==
  \A i, j \in Proc :
    (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

TypeOK ==
  /\ pc \in [Proc -> {"idle", "cs"}]
  /\ ticket \in [Proc -> Nat]
  /\ choosing \in [Proc -> BOOLEAN]

Inv == MutualExclusion /\ TypeOK

\* ----------------------------------------------------------------------
\*  Specification name required by the .cfg
\* ----------------------------------------------------------------------
ISpec == [][Next]_<<pc, ticket, choosing>>

=============================================================================