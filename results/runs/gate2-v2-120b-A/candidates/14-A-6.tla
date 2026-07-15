---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

(*-----------------------------------------------------------------
  Constants (provided by the .cfg file)
-----------------------------------------------------------------*)
CONSTANT N       \* number of processes, set to 3 in the .cfg
CONSTANT MaxNat  \* maximum value for the overridden Nat, set to 3
CONSTANT Nat     \* finite range 0..MaxNat, defined in the .cfg

(*-----------------------------------------------------------------
  Set of process identifiers
-----------------------------------------------------------------*)
Proc == 0 .. N-1

(*-----------------------------------------------------------------
  State variables (from the Boulanger specification)
-----------------------------------------------------------------*)
VARIABLES pc,                 \* program counters: "idle", "trying", "cs"
          ticket,             \* ticket numbers for each process
          nextTicket,         \* next ticket to assign
          using               \* set of processes currently in CS

(*-----------------------------------------------------------------
  Type definitions (helpful for readability)
-----------------------------------------------------------------*)
PCVals == {"idle", "trying", "cs"}

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ pc = [i \in Proc |-> "idle"]
  /\ ticket = [i \in Proc |-> 0]
  /\ nextTicket = 0
  /\ using = {}

(*-----------------------------------------------------------------
  Actions (inherited from the original Boulanger specification)
-----------------------------------------------------------------*)
Acquire(i) ==
  /\ pc[i] = "idle"
  /\ ticket[i] = 0
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ pc' = [pc EXCEPT ![i] = "trying"]
  /\ UNCHANGED using

Try(i) ==
  /\ pc[i] = "trying"
  /\ \A j \in Proc :
        (j # i) =>
          \/ ticket[i] < ticket[j]
          \/ (ticket[i] = ticket[j] /\ i < j)
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<ticket, nextTicket, using>>

Release(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED <<nextTicket, using>>

EnterCS(i) ==
  /\ pc[i] = "cs"
  /\ using' = using \cup {i}
  /\ UNCHANGED <<pc, ticket, nextTicket>>

ExitCS(i) ==
  /\ i \in using
  /\ using' = using \ {i}
  /\ UNCHANGED <<pc, ticket, nextTicket>>

(*-----------------------------------------------------------------
  Next-state relation (any enabled action for any process)
-----------------------------------------------------------------*)
Next ==
  \E i \in Proc :
    \/ Acquire(i)
    \/ Try(i)
    \/ Release(i)
    \/ EnterCS(i)
    \/ ExitCS(i)

(*-----------------------------------------------------------------
  State constraint: keep ticket numbers strictly below MaxNat
-----------------------------------------------------------------*)
StateConstraint ==
  \A i \in Proc : ticket[i] < MaxNat

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
MutualExclusion ==
  \A i, j \in Proc :
    (i # j) => ~(i \in using /\ j \in using)

TypeOK ==
  /\ pc \in [Proc -> PCVals]
  /\ ticket \in [Proc -> Nat]
  /\ nextTicket \in Nat
  /\ using \subseteq Proc

Inv == MutualExclusion /\ TypeOK

(*-----------------------------------------------------------------
  Specification, invariants, and properties required by the cfg
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, ticket, nextTicket, using>>

=============================================================================