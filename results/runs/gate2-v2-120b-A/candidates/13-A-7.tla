---- MODULE MCBakery ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANT N, MaxNat, Nat

\* Number of processes
Proc == 1..N

\* State variables
VARIABLES pc, ticket

\* pc[p] is the program counter for process p
\* ticket[p] is the current ticket number of process p (0 means no ticket)

\* Initial state
Init ==
  /\ pc = [p \in Proc |-> "idle"]
  /\ ticket = [p \in Proc |-> 0]

\* Type-correctness predicate (used as an invariant)
TypeOK ==
  /\ pc \in [Proc -> {"idle", "wait", "cs"}]
  /\ ticket \in [Proc -> Nat]

\* Mutual exclusion predicate
MutualExclusion ==
  \A p, q \in Proc :
    (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Full inductive invariant (type correctness + mutual exclusion)
Inv == TypeOK /\ MutualExclusion

\* Helper to compute the minimum ticket among processes currently in the
\* waiting or critical sections.
MinTicket ==
  LET active == { p \in Proc : pc[p] \in {"wait", "cs"} } IN
    IF active = {} THEN 0
    ELSE Min({ ticket[p] : p \in active })

\* Actions
Acquire(p) ==
  /\ pc[p] = "idle"
  /\ ticket' = [ticket EXCEPT ![p] = 1 + Max({ ticket[q] : q \in Proc })]
  /\ pc' = [pc EXCEPT ![p] = "wait"]
  /\ UNCHANGED Nat

Enter(p) ==
  /\ pc[p] = "wait"
  /\ ticket[p] = MinTicket
  /\ \A q \in Proc :
        (q # p) => (pc[q] # "cs" \/ ticket[q] # ticket[p])
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED ticket

Exit(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED Nat

\* Next-state relation
Next ==
  \E p \in Proc :
    Acquire(p) \/ Enter(p) \/ Exit(p)

\* The inductive specification (starting from any type-correct state)
ISpec ==
  Init /\ [][Next]_<<pc, ticket>>

\* Safety properties (declared as invariants for the .cfg)
MutualExclusionInv == MutualExclusion
TypeOKInv == TypeOK
InvInv == Inv

\* The SPECIFICATION formula required by the .cfg
Spec == ISpec

=============================================================================