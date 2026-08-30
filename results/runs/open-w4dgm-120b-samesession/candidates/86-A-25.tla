---- MODULE TLAPS ----
EXTENDS Integers, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, Spass, LS4

Backends == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, Spass, LS4}

VARIABLES sent, received, dispatched, proved

vars == <<sent, received, dispatched, proved>>

TypeOK ==
  /\ sent \subseteq Backends
  /\ received \subseteq Backends
  /\ dispatched \subseteq Backends
  /\ proved \subseteq Backends

Init ==
  /\ sent = {}
  /\ received = {}
  /\ dispatched = {}
  /\ proved = {}

Send(b) ==
  /\ b \notin sent
  /\ sent' = sent \cup {b}
  /\ UNCHANGED <<received, dispatched, proved>>

Receive(b) ==
  /\ b \in sent
  /\ b \notin received
  /\ received' = received \cup {b}
  /\ UNCHANGED <<sent, dispatched, proved>>

Dispatch(b) ==
  /\ b \in received
  /\ b \notin dispatched
  /\ dispatched' = dispatched \cup {b}
  /\ UNCHANGED <<sent, received, proved>>

Prove(b) ==
  /\ b \in dispatched
  /\ b \notin proved
  /\ proved' = proved \cup {b}
  /\ UNCHANGED <<sent, received, dispatched>>

Idle == UNCHANGED vars

Next ==
  \/ \E b \in Backends : Send(b)
  \/ \E b \in Backends : Receive(b)
  \/ \E b \in Backends : Dispatch(b)
  \/ \E b \in Backends : Prove(b)
  \/ Idle

Spec == Init /\ [][Next]_vars

SetExtensionality ==
  \A X, Y \in SUBSET Backends : (\A x \in Backends : (x \in X) <=> (x \in Y)) => X = Y

NoSetContainsAllValues ==
  \A X \in SUBSET Backends : X = Backends => FALSE

AllProved == \A b \in Backends : b \in proved

====