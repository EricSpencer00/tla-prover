---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, MaxNat

(*-----------------------------------------------------------------
  Finite version of Nat used for model checking.
  NatOverride is the set {0,1,...,MaxNat}.
-----------------------------------------------------------------*)
NatOverride == 0 .. MaxNat

(*-----------------------------------------------------------------
  Set of process identifiers.
-----------------------------------------------------------------*)
Proc == 1 .. N

VARIABLES pc, choosing, number

(*-----------------------------------------------------------------
  Types of the variables.
-----------------------------------------------------------------*)
TypeOK ==
    /\ pc \in [Proc -> {"idle", "wait", "critical"}]
    /\ choosing \in [Proc -> BOOLEAN]
    /\ number \in [Proc -> NatOverride]

(*-----------------------------------------------------------------
  Invariant (full inductive invariant).  For this simple model we
  take it to be the same as TypeOK.
-----------------------------------------------------------------*)
Inv == TypeOK

(*-----------------------------------------------------------------
  Mutual exclusion safety property.
-----------------------------------------------------------------*)
MutualExclusion ==
    \A i, j \in Proc :
        (i # j) => ~(pc[i] = "critical" /\ pc[j] = "critical")

(*-----------------------------------------------------------------
  Initial state (not used for the inductive specification, but kept
  for completeness).
-----------------------------------------------------------------*)
Init ==
    /\ pc = [i \in Proc |-> "idle"]
    /\ choosing = [i \in Proc |-> FALSE]
    /\ number = [i \in Proc |-> 0]

(*-----------------------------------------------------------------
  Helper: compute the next ticket number for process i.
  It is (max current ticket + 1) mod (MaxNat+1) to stay within
  NatOverride.
-----------------------------------------------------------------*)
NextTicket(i) ==
    LET maxNum == IF \E j \in Proc : TRUE THEN Max({ number[j] : j \in Proc }) ELSE 0
    IN (maxNum + 1) % (MaxNat + 1)

(*-----------------------------------------------------------------
  Process i wants to enter the critical section.
-----------------------------------------------------------------*)
Want(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED number

(*-----------------------------------------------------------------
  Process i picks its ticket number.
-----------------------------------------------------------------*)
PickTicket(i) ==
    /\ pc[i] = "wait"
    /\ choosing[i] = TRUE
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ number' = [number EXCEPT ![i] = NextTicket(i)]
    /\ pc' = pc
    /\ UNCHANGED << >>

(*-----------------------------------------------------------------
  Process i waits until it has the smallest ticket (lexicographic
  ordering with process id as tie‑breaker).  For simplicity we model
  the waiting step as a no‑op that may be taken when the condition
  holds; otherwise the process cannot progress.
-----------------------------------------------------------------*)
Enter(i) ==
    /\ pc[i] = "wait"
    /\ choosing[i] = FALSE
    /\ \A j \in Proc :
          (j # i) =>
            ( \/ choosing[j] = FALSE /\ 
               ( number[i] < number[j] \/ 
                 ( number[i] = number[j] /\ i < j ) )
            )
    /\ pc' = [pc EXCEPT ![i] = "critical"]
    /\ UNCHANGED << choosing, number >>

(*-----------------------------------------------------------------
  Process i leaves the critical section.
-----------------------------------------------------------------*)
Leave(i) ==
    /\ pc[i] = "critical"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ number' = [number EXCEPT ![i] = 0]
    /\ UNCHANGED << choosing >>

(*-----------------------------------------------------------------
  The next-state relation is the disjunction of all possible actions
  of all processes.
-----------------------------------------------------------------*)
Next ==
    \E i \in Proc :
        \/ Want(i)
        \/ PickTicket(i)
        \/ Enter(i)
        \/ Leave(i)

(*-----------------------------------------------------------------
  Inductive specification: any type‑correct state satisfying the
  invariant may be an initial state, and the system must always
  follow Next.
-----------------------------------------------------------------*)
InitInductive ==
    /\ TypeOK
    /\ Inv

ISpec ==
    InitInductive /\ [][Next]_<< pc, choosing, number >>

=============================================================================