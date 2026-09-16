---- MODULE W4Od19m7p2t1 ----
EXTENDS Naturals
CONSTANTS Patrons, Total

None == "none"

VARIABLES reg, shelf, loaned, inbox
vars == <<reg, shelf, loaned, inbox>>

Msgs == [patron : Patrons, act : {"borrow", "return"}]

Init ==
  /\ reg = None
  /\ shelf = Total
  /\ loaned = 0
  /\ inbox = {}

Request(p, a) ==
  /\ [patron : p, act |-> a] \notin inbox
  /\ inbox' = inbox \cup {[patron |-> p, act |-> a]}
  /\ UNCHANGED <<reg, shelf, loaned>>

Acquire(p) ==
  /\ reg = None
  /\ reg' = p
  /\ UNCHANGED <<shelf, loaned, inbox>>

Borrow(p) ==
  /\ reg = p
  /\ shelf > 0
  /\ [patron |-> p, act |-> "borrow"] \in inbox
  /\ shelf' = shelf - 1
  /\ loaned' = loaned + 1
  /\ inbox' = inbox \ {[patron |-> p, act |-> "borrow"]}
  /\ reg' = None

Return(p) ==
  /\ reg = p
  /\ loaned > 0
  /\ [patron |-> p, act |-> "return"] \in inbox
  /\ loaned' = loaned - 1
  /\ shelf' = shelf + 1
  /\ inbox' = inbox \ {[patron |-> p, act |-> "return"]}
  /\ reg' = None

Release(p) ==
  /\ reg = p
  /\ reg' = None
  /\ UNCHANGED <<shelf, loaned, inbox>>

Next ==
  \/ \E p \in Patrons, a \in {"borrow", "return"} : Request(p, a)
  \/ \E p \in Patrons : Acquire(p) \/ Borrow(p) \/ Return(p) \/ Release(p)

Spec == Init /\ [][Next]_vars

CopiesConserved == shelf + loaned = Total
====