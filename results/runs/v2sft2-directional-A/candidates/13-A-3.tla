---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, MaxNat, Nat

\* Override the infinite Nat set with a finite range
Nat == 0 .. MaxNat

VARIABLES tickets, pos, cs

\* -----------------------------
\* Initial condition
\* -----------------------------
Init ==
  /\ tickets = [i \in 1..N |-> 0]
  /\ pos     = [i \in 1..N |-> 0]
  /\ cs      = {}

\* -----------------------------
\* Helper: choose the smallest unused ticket
\* -----------------------------
MinUnusedTicket ==
  LET Unused == { n \in Nat : \A i \in 1..N : n # tickets[i] }
  IN  CHOOSE n \in Unused : TRUE

\* -----------------------------
\* Actions for process i
\* -----------------------------
TakeTicket(i) ==
  /\ tickets[i] = 0
  /\ tickets' = [tickets EXCEPT ![i] = MinUnusedTicket]
  /\ UNCHANGED <<pos, cs>>

EnterCritical(i) ==
  /\ tickets[i] # 0
  /\ pos[i] = 0
  /\ { j \in 1..N :
        tickets[j] # 0
        /\ (tickets[j] < tickets[i]
            \/ (tickets[j] = tickets[i] /\ j < i)) } = {}
  /\ cs' = cs \cup {i}
  /\ UNCHANGED <<tickets, pos>>

LeaveCritical(i) ==
  /\ i \in cs
  /\ cs' = cs \ {i}
  /\ pos[i] = 1
  /\ UNCHANGED <<tickets, pos>>

Rest(i) ==
  /\ tickets[i] # 0
  /\ \E j \in 1..N :
        tickets[j] # 0
        /\ (tickets[j] < tickets[i]
            \/ (tickets[j] = tickets[i] /\ j <= i))
      => pos[i] = 1
  /\ UNCHANGED <<tickets, pos, cs>>

\* -----------------------------
\* Next-state relation
\* -----------------------------
Next ==
  \E i \in 1..N :
    \/ TakeTicket(i)
    \/ EnterCritical(i)
    \/ LeaveCritical(i)
    \/ Rest(i)

\* -----------------------------
\* Specification for inductive checking
\* -----------------------------
ISpec ==
  Init /\ [][Next]_<<tickets, pos, cs>>

\* -----------------------------
\* Invariants
\* -----------------------------
MutualExclusion ==
  \A i, j \in cs : i = j

TypeOK ==
  /\ tickets \in [1..N -> Nat]
  /\ pos     \in [1..N -> {0,1}]
  /\ cs      \in SUBSET 1..N

Inv ==
  \A i, j \in 1..N :
    /\ tickets[i] # 0 /\ tickets[j] # 0
    => tickets[i] # tickets[j]
  /\ \A i \in cs :
    /\ tickets[i] # 0
    /\ pos[i] = 1

====