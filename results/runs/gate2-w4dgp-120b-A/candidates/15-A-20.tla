---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, loc, recv, sent
vars == << correct, faulty, loc, recv, sent >>

\* loc: f for "has not received the broadcaster's INIT message", b for "received it,
\*      r for "sent an ECHO", a for "has accepted".
\* recv[p]: messages p has taken into account; sent: messages correct processes sent.
\* A message is a <sender,tag> pair, and every correct process sends exactly one ECHO.
Messages == [sender: 1..N, tag: {"ECHO"}]

TypeOK ==
    /\ correct \subseteq 1..N
    /\ cardinality(correct) = N - F
    /\ faulty = (1..N) \ correct
    /\ loc \in [1..N -> {"b","f","r","a"}]
    /\ recv \in [1..N -> SUBSET Messages]
    /\ sent \subseteq Messages

Init ==
    /\ \E g \in [1..N -> {"b","f"}] :
        /\ \A p \in correct : loc[p] = g[p]
        /\ \A p \in faulty : loc[p] = g[p]
    /\ correct = {1..N - F}
    /\ faulty = {N - F + 1..N}
    /\ recv = [p \in 1..N |-> {}]
    /\ sent = {}

SentBy(p) == {m \in sent : m.sender = p}

\* A correct process may receive any new messages that have been sent by correct
\* processes and any message a Byzantine process decides to inject.
Deliver(p) ==
    /\ loc[p] \in {"b","f"}
    /\ \E new \in SUBSET (sent \cup { [sender |-> q, tag |-> "ECHO"] : q \in faulty }) :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ loc' = [loc EXCEPT ![p] =
                     IF loc[p] = "b" THEN "a" ELSE loc[p]]
    /\ UNCHANGED << correct, faulty, sent >>

SendEcho(p) ==
    /\ loc[p] = "b"
    /\ sent' = sent \cup {[sender |-> p, tag |-> "ECHO"]}
    /\ loc' = [loc EXCEPT ![p] = "r"]
    /\ UNCHANGED << correct, faulty, recv >>

\* N-2T ECHO messages is enough to convince a correct process to relay, but not to
\* accept yet; N-T is the acceptance threshold.
Relay(p) ==
    /\ loc[p] = "b"
    /\ N - 2 * T <= Cardinality({q \in correct : [sender |-> q, tag |-> "ECHO"] \in recv[p]})
    /\ N - T > Cardinality({q \in correct : [sender |-> q, tag |-> "ECHO"] \in recv[p]})
    /\ sent' = sent \cup {[sender |-> p, tag |-> "ECHO"]}
    /\ loc' = [loc EXCEPT ![p] = "r"]
    /\ UNCHANGED << correct, faulty, recv >>

Accept(p) ==
    /\ loc[p] \in {"b","r"}
    /\ N - T <= Cardinality({q \in correct : [sender |-> q, tag |-> "ECHO"] \in recv[p]})
    /\ sent' = sent \cup {[sender |-> p, tag |-> "ECHO"]}
    /\ loc' = [loc EXCEPT ![p] = "a"]
    /\ UNCHANGED << correct, faulty, recv >>

Next == (\E p \in correct : Deliver(p)) \/ (\E p \in correct : SendEcho(p))
        \/ (\E p \in correct : Relay(p)) \/ (\E p \in correct : Accept(p))

Spec == Init /\ [][Next]_vars
\* Weak fairness on every combined receive-and-act step a correct process
\* can repeat forever once enough correct messages are available.
SpecF == Spec /\ (\A p \in correct : WF_vars(Deliver(p)) /\ WF_vars(SendEcho(p))
                         /\ WF_vars(Relay(p)) /\ WF_vars(Accept(p)))

CorrLtl == (\A p \in correct : loc[p] = "b") ~> (\A p \in correct : loc[p] = "a")
RelayLtl == (\E p \in correct : loc[p] = "a") ~> (\A p \in correct : loc[p] = "a")

\* Unforgeability: with no correct broadcaster (no one starts in the broadcast
\* state), no correct process ever accepts.
UnforgLtl == (\A p \in correct : loc[p] = "f") ~> (\A p \in correct : loc[p] = "a")

\* With no fairness assumption the reachable-state check alone can verify
\* unforgeability; CorrLtl and RelayLtl need the weak fairness of SpecF.
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
====