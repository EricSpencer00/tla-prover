---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT N
CONSTANT MaxNat
CONSTANT Nat

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
\* The finite set that replaces the infinite set of natural numbers.
NatSet == 0 .. MaxNat

(*--------------------------------------------------------------------
  State variables (as in the original Bakery specification)
--------------------------------------------------------------------*)
VARIABLES pc, ticket, choosing

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
ProcSet == 1 .. N

CriticalSection == "cs"
NonCriticalSection == "ncs"
EntrySection == "entry"
WaitSection == "wait"

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ pc = [p \in ProcSet |-> NonCriticalSection]
  /\ ticket = [p \in ProcSet |-> 0]
  /\ choosing = [p \in ProcSet |-> FALSE]

(*--------------------------------------------------------------------
  Actions (identical to those of the original Bakery algorithm)
--------------------------------------------------------------------*)
Entry(p) ==
  /\ pc[p] = NonCriticalSection
  /\ pc' = [pc EXCEPT ![p] = EntrySection]
  /\ UNCHANGED <<ticket, choosing>>

Exit(p) ==
  /\ pc[p] = CriticalSection
  /\ pc' = [pc EXCEPT ![p] = NonCriticalSection]
  /\ UNCHANGED <<ticket, choosing>>

FinishChoosing(p) ==
  /\ pc[p] = EntrySection
  /\ choosing' = [choosing EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<pc, ticket>>

UpdateTicket(p) ==
  /\ pc[p] = EntrySection
  /\ choosing[p] = FALSE
  /\ ticket' = [ticket EXCEPT ![p] = 
        1 + Max({ ticket[q] : q \in ProcSet })]
  /\ choosing' = [choosing EXCEPT ![p] = TRUE]
  /\ UNCHANGED pc

Wait(p) ==
  /\ pc[p] = EntrySection
  /\ choosing[p] = FALSE
  /\ \A q \in ProcSet :
        (q # p) => 
          ~choosing[q] /\ 
          (ticket[q] = 0 \/ ticket[q] > ticket[p] \/ 
           (ticket[q] = ticket[p] /\ q > p))
  /\ pc' = [pc EXCEPT ![p] = CriticalSection]
  /\ UNCHANGED <<ticket, choosing>>

Next ==
  \E p \in ProcSet :
    \/ Entry(p)
    \/ Exit(p)
    \/ FinishChoosing(p)
    \/ UpdateTicket(p)
    \/ Wait(p)

(*--------------------------------------------------------------------
  Specification (inductive)
--------------------------------------------------------------------*)
ISpec == Init /\ [][Next]_<<pc, ticket, choosing>>

(*--------------------------------------------------------------------
  Invariant definitions
--------------------------------------------------------------------*)
MutualExclusion ==
  ~(\E i, j \in ProcSet : i # j /\ pc[i] = CriticalSection /\ pc[j] = CriticalSection)

TypeOK ==
  /\ pc \in [ProcSet -> {NonCriticalSection, EntrySection, CriticalSection}]
  /\ ticket \in [ProcSet -> NatSet]
  /\ choosing \in [ProcSet -> BOOLEAN]

Inv == MutualExclusion /\ TypeOK

(*--------------------------------------------------------------------
  The specification name required by the .cfg file
--------------------------------------------------------------------*)
Spec == ISpec

(*--------------------------------------------------------------------
  THEOREMS (optional, but useful for model checking)
--------------------------------------------------------------------*)
THEOREM Spec => []Inv

====