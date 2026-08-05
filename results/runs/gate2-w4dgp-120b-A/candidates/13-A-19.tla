---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES ticket, inCS, using, usedSet

vars == <<ticket, inCS, using, usedSet>>
\* The natural-number type is overridden globally in the .cfg so that
\* all ticket numbers stay within 0..MaxNat; the module itself keeps the
\* full set of actions of the Bakery algorithm, only the range of Nat is
\* constrained at model-check time.

Init ==
  /\ ticket = [p \in 1..N |-> 0]
  /\ inCS = FALSE
  /\ using = 0
  /\ usedSet = {}

Acquire(p) ==
  /\ ticket[p] = 0
  /\ ticket' = [ticket EXCEPT ![p] = 1 + usedSet]
  /\ UNCHANGED <<inCS, using, usedSet>>

Enter(p) ==
  /\ ticket[p] # 0
  /\ ~inCS
  /\ \A q \in 1..N : ticket[q] = 0 \/ ticket[q] > ticket[p]
  /\ inCS' = TRUE
  /\ using' = p
  /\ UNCHANGED <<ticket, usedSet>>

Release(p) ==
  /\ inCS
  /\ using = p
  /\ inCS' = FALSE
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ usedSet' = usedSet \cup {ticket[p]}
  /\ UNCHANGED using

Next ==
  \/ \E p \in 1..N : Acquire(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Release(p)

ISpec == Init /\ [][Next]_vars

MutexInv ==
  /\ inCS => using \in 1..N
  /\ (using # 0) => inCS

TypeOK ==
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ inCS \in BOOLEAN
  /\ using \in 0..N
  /\ usedSet \subseteq (0..MaxNat)

Inv == MutexInv /\ TypeOK

====