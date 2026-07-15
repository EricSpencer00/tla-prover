---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, MaxNat, Nat

\* Derived constant for the set of process identifiers
ProcSet == 1 .. N

\* State variables (inherited from the Bakery specification)
VARIABLES ticket, choosing, pc

\* ticket  : [ProcSet -> Nat]   each process's ticket number
\* choosing: [ProcSet -> BOOLEAN]  true while a process is picking its ticket
\* pc      : [ProcSet -> {"idle", "choose", "wait", "cs", "exit"}]
\*          program counter indicating the current phase of each process

\* Type correctness predicate
TypeOK == 
   /\ ticket \in [ProcSet -> Nat]
   /\ choosing \in [ProcSet -> BOOLEAN]
   /\ pc \in [ProcSet -> {"idle", "choose", "wait", "cs", "exit"}]

\* Initial state (type-correct and all processes idle)
Init ==
   /\ ticket = [i \in ProcSet |-> 0]
   /\ choosing = [i \in ProcSet |-> FALSE]
   /\ pc = [i \in ProcSet |-> "idle"]
   /\ TypeOK

\* Action: a process starts the entry protocol
Start(i) ==
   /\ pc[i] = "idle"
   /\ pc' = [pc EXCEPT ![i] = "choose"]
   /\ choosing' = [choosing EXCEPT ![i] = TRUE]
   /\ UNCHANGED ticket

\* Action: the process picks a ticket number
Choose(i) ==
   /\ pc[i] = "choose"
   /\ ticket' = [ticket EXCEPT ![i] = 1 + Max({ticket[j] : j \in ProcSet})]
   /\ choosing' = [choosing EXCEPT ![i] = FALSE]
   /\ pc' = [pc EXCEPT ![i] = "wait"]
   /\ ticket[i] \in Nat   \* respects the overridden Nat set

\* Helper: ordering relation used in the wait phase
Before(i, j) ==
   /\ ticket[i] < ticket[j]
   \/ (ticket[i] = ticket[j] /\ i < j)

\* Action: the process waits until it is its turn
Wait(i) ==
   /\ pc[i] = "wait"
   /\ \A j \in ProcSet :
        (j # i) => 
          ( (pc[j] # "cs") 
            \/ ( (pc[j] = "wait") => ~Before(j,i) ) )
   /\ pc' = [pc EXCEPT ![i] = "cs"]
   /\ UNCHANGED <<ticket, choosing>>

\* Action: the process exits the critical section
Exit(i) ==
   /\ pc[i] = "cs"
   /\ pc' = [pc EXCEPT ![i] = "exit"]
   /\ UNCHANGED <<ticket, choosing>>

\* Action: the process returns to idle, resetting its ticket
Done(i) ==
   /\ pc[i] = "exit"
   /\ pc' = [pc EXCEPT ![i] = "idle"]
   /\ ticket' = [ticket EXCEPT ![i] = 0]
   /\ UNCHANGED choosing

\* The overall NEXT relation (any enabled action of any process)
Next ==
   \/ \E i \in ProcSet : Start(i)
   \/ \E i \in ProcSet : Choose(i)
   \/ \E i \in ProcSet : Wait(i)
   \/ \E i \in ProcSet : Exit(i)
   \/ \E i \in ProcSet : Done(i)

\* Safety invariant: mutual exclusion
MutualExclusion ==
   \A i, j \in ProcSet : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

\* Full inductive invariant (type correctness + safety)
Inv == TypeOK /\ MutualExclusion

\* Specification used for model checking (inductive start)
ISpec == Init /\ [] [Next]_<<ticket, choosing, pc>>

====