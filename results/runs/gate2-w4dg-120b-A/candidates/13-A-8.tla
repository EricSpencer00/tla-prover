---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

N == 2
MaxNat == 2
Nat == 0 .. MaxNat

VARIABLES cs, waiting, ticket, nextTicket
vars == <<cs, waiting, ticket, nextTicket>>

TypeOK ==
  /\ cs \in [1 .. N -> BOOLEAN]
  /\ waiting \in SUBSET (1 .. N)
  /\ ticket \in [1 .. N -> Nat]
  /\ nextTicket \in Nat

MutualExclusion ==
  \A i \in 1 .. N, j \in 1 .. N : (cs[i] /\ cs[j]) => (i = j)

Init ==
  /\ cs = [i \in 1 .. N |-> FALSE]
  /\ waiting = {}
  /\ ticket = [i \in 1 .. N |-> 0]
  /\ nextTicket = 0

Request(i) ==
  /\ i \notin waiting
  /\ ~cs[i]
  /\ nextTicket < MaxNat
  /\ waiting' = waiting \cup {i}
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED cs

Enter(i) ==
  /\ i \in waiting
  /\ \A j \in waiting : ticket[i] <= ticket[j]
  /\ ~cs[i]
  /\ cs' = [cs EXCEPT ![i] = TRUE]
  /\ waiting' = waiting \ {i}
  /\ UNCHANGED <<ticket, nextTicket>>

Exit(i) ==
  /\ cs[i]
  /\ cs' = [cs EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<waiting, ticket, nextTicket>>

Next ==
  \E i \in 1 .. N :
    \/ Request(i)
    \/ Enter(i)
    \/ Exit(i)

Inv == TypeOK /\ MutualExclusion

Spec == Init /\ [][Next]_vars

ISpec == Spec /\ WF_vars(Exit(1) \/ Exit(2))

====