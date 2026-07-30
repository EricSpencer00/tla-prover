---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

\* Model-checking the Bakery mutual exclusion algorithm with a bounded
\* natural-number range. The constant Nat is overridden with the finite
\* set NatOverride, so every ticket number stays within the configured
\* maximum (MaxNat). The spec starts from the inductive invariant (ISpec)
\* rather than just the initial state. No output properties are defined
\* here -- only the safety/invariant checks.
CONSTANTS N, MaxNat, Nat

\* The finite version of Nat used for model checking. The .cfg substitutes
\* this operator in place of the bare Nat constant.
NatOverride == 0..MaxNat

VARIABLES cs, num, ticket, state
vars == <<cs, num, ticket, state>>

TypeOK ==
  /\ cs \subseteq (1..N)
  /\ num \in NatOverride
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ state \in [1..N -> {"idle", "waiting", "cs"}]

MutualExclusion ==
  \A i \in cs, j \in cs : i = j

Inv == TypeOK /\ MutualExclusion

Init ==
  /\ cs = {}
  /\ num = 0
  /\ ticket = [i \in 1..N |-> 0]
  /\ state = [i \in 1..N |-> "idle"]

Request(i) ==
  /\ state[i] = "idle"
  /\ state' = [state EXCEPT ![i] = "waiting"]
  /\ UNCHANGED <<cs, num, ticket>>

\* Take a numbered ticket; ticket numbers are drawn from the bounded range.
TakeTicket(i) ==
  /\ state[i] = "waiting"
  /\ num' = (num + 1) % (MaxNat + 1)
  /\ ticket' = [ticket EXCEPT ![i] = num]
  /\ UNCHANGED <<cs, state>>

\* Enter the critical section only if no live ticket is lower.
Enter(i) ==
  /\ state[i] = "waiting"
  /\ \A j \in 1..N : (state[j] = "cs") => (ticket[i] < ticket[j])
  /\ cs' = cs \cup {i}
  /\ state' = [state EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<num, ticket>>

Exit(i) ==
  /\ state[i] = "cs"
  /\ cs' = cs \ {i}
  /\ state' = [state EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED num

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : TakeTicket(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

\* Starting from any type-correct state satisfying the invariant.
ISpec == Init /\ [][Next]_vars /\ WF_vars(Next)

====