---- MODULE bcastByz ----
\* This module models a parameterized reliable broadcast with Byzantine faults (Srikanth &
\* Toueg '87, Fig. 7). Actions: Init, Receive, Echo, Echo2, Accept. It checks that no
\* correct process accepts unless at least one correct process broadcasted first.
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

Locations == {"none", "hasInit", "echoed", "accepted"}

VARIABLES correct, faulty, pc, inbox, sent

vars == <<correct, faulty, pc, inbox, sent>>

\* TypeOK: every variable stays inside its domain; FCConstraints: the partition and
\* message cardinalities respect the fault bound T.
TypeOK ==
  /\ correct \subseteq (0..(N - 1))
  /\ faulty \subseteq (0..(N - 1))
  /\ pc \in [0..(N - 1) -> Locations]
  /\ inbox \in [0..(N - 1) -> SUBSET (0..(N - 1) \X {"ECHO"})]
  /\ sent \subseteq (0..(N - 1) \X {"ECHO"})

FCConstraints ==
  /\ N > (3 * T)
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(correct) = (N - F)
  /\ correct \cap faulty = {}
  /\ correct \cup faulty = (0..(N - 1))

Init ==
  /\ correct \subseteq (0..(N - 1))
  /\ faulty = ((0..(N - 1)) \ correct)
  /\ pc \in [0..(N - 1) -> Locations]
  /\ inbox = [p \in (0..(N - 1)) |-> {}]
  /\ sent = {}

\* A correct process receives any new messages it can: all sent by correct processes
\* plus any message a Byzantine process might forge.
Receive(p) ==
  /\ p \in correct
  /\ \E fresh \in SUBSET (([0..(N - 1)] \X {"ECHO"}) \ union sent) :
       inbox' = [inbox EXCEPT ![p] = @ \cup fresh]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* A correct process that received the INIT message (starts in hasInit) immediately
\* accepts and sends an ECHO to everyone.
Echo(p) ==
  /\ p \in correct
  /\ pc[p] = "hasInit"
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

\* A correct process that has not yet sent an ECHO accepts enough ECHO messages
\* (between N-2T and N-T) and sends one.
Echo2(p) ==
  /\ p \in correct
  /\ pc[p] = "none"
  /\ N - (2 * T) <= Cardinality(inbox[p])
  /\ Cardinality(inbox[p]) < (N - T)
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

\* A correct process that has not yet sent an ECHO receives at least N-T ECHO messages
\* and sends one while also accepting.
Accept(p) ==
  /\ p \in correct
  /\ pc[p] = "none"
  /\ Cardinality(inbox[p]) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

\* A correct process that has already sent its ECHO accepts once it has enough.
Accept2(p) ==
  /\ p \in correct
  /\ pc[p] = "echoed"
  /\ Cardinality(inbox[p]) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, inbox, sent>>

Next ==
  \/ \E p \in (0..(N - 1)) : Receive(p)
  \/ \E p \in (0..(N - 1)) : Echo(p)
  \/ \E p \in (0..(N - 1)) : Echo2(p)
  \/ \E p \in (0..(N - 1)) : Accept(p)
  \/ \E p \in (0..(N - 1)) : Accept2(p)

Spec == Init /\ [][Next]_vars

CorrLtl == (\A p \in (0..(N - 1)) : pc[p] = "hasInit") ~> (\A p \in (0..(N - 1)) : pc[p] = "accepted")
RelayLtl == (\E p \in (0..(N - 1)) : pc[p] = "accepted") ~> (\A p \in (0..(N - 1)) : pc[p] = "accepted")
UnforgLtl == (\A p \in correct : pc[p] = "none") ~> (\A p \in correct : pc[p] = "none")

====