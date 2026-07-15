---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, MaxNat, Nat

\* The set Nat is overridden to be the finite range 0..MaxNat.
Nat == 0 .. MaxNat

\* Processes are identified by numbers 0 through N-1.
Proc == 0 .. (N - 1)

VARIABLES pc, ticket

\* pc[p] ∈ {"idle", "wait", "cs"} : program counter of process p
\* ticket[p] ∈ Nat                : ticket number of process p
vars == <<pc, ticket>>

\* Initial state: all processes are idle and have ticket 0.
Init ==
  /\ pc = [p \in Proc |-> "idle"]
  /\ ticket = [p \in Proc |-> 0]

\* Process p requests the critical section.
Request(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "wait"]
  /\ ticket' = [ticket EXCEPT ![p] = 1 + Max({ ticket[q] : q \in Proc })]

\* Process p checks that its ticket is the smallest (lexicographic order).
Enter(p) ==
  /\ pc[p] = "wait"
  /\ \A q \in Proc :
        ( q # p ) => (
          ( ticket[p] < ticket[q] ) \/
          ( ticket[p] = ticket[q] /\ p < q )
        )
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED ticket

\* Process p leaves the critical section.
Leave(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]

Next ==
  \/ \E p \in Proc : Request(p)
  \/ \E p \in Proc : Enter(p)
  \/ \E p \in Proc : Leave(p)

\* Safety invariant: at most one process is in the critical section.
MutualExclusion ==
  \A p, q \in Proc :
      (p # q) => ~ (pc[p] = "cs" /\ pc[q] = "cs")

\* Type correctness invariant.
TypeOK ==
  /\ pc \in [Proc -> {"idle", "wait", "cs"}]
  /\ ticket \in [Proc -> Nat]

\* Full inductive invariant (captures safety and type correctness).
Inv == MutualExclusion /\ TypeOK

\* The specification used for model checking (inductive spec).
ISpec == Init /\ [][Next]_vars

\* The specification expression required by the .cfg file.
Spec == ISpec

====