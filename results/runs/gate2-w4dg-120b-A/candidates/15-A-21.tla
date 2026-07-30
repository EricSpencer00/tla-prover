---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

\* A reliable broadcast from Srikanth and Toueg (1987), with Byzantine
\* participants. N and T are deliberately small constants here for model
\* checking only; the node sets, message sets, and counters keep their
\* declared bounds at all times (TypeOK). UnforgLtl captures the
\* unforgeability condition: no correct process accepts when nobody
\* broadcast. CorrLtl and RelayLtl are the two liveness claims.

CONSTANTS N, T, F

\* Correct: nodes running the protocol; Faulty: Byzantine nodes.
\* Phase: control location per node. Recv: messages each node has taken in.
\* Sent: the total set of messages sent by correct nodes.
VARIABLES correct, faulty, phase, recv, sent

vars == <<correct, faulty, phase, recv, sent>>

Phases == {"init", "none", "echo", "accept"}
Msgs == {<<"echo", n>> : n \in 1 .. N}

\* Models a node receiving a bulk of in-flight messages now.
RECURSIVE Bundle(_)
Bundle(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE IN {x} \cup Bundle(S \ {x})

InitX ==
    {p \in 1 .. N : CHOOSE q \in 1 .. N : TRUE}
    \cup
    {p \in 1 .. N : CHOOSE q \in 1 .. N :
        Cardinality({x \in 1 .. N : p = x}) = 0}

Init0 ==
    {p \in 1 .. N : CHOOSE q \in 1 .. N :
        Cardinality({x \in 1 .. N : p = x}) = 0}
    \cup
    {p \in 1 .. N : CHOOSE q \in 1 .. N : TRUE}

Init ==
    /\ Cardinality(correct) = N - F
    /\ faulty = (1 .. N) \ correct
    /\ \A p \in 1 .. N : phase[p] \in Phases
    /\ \A p \in 1 .. N : recv[p] \in SUBSET Msgs
    /\ sent = {}
    /\ phase \in [1 .. N -> Phases]

\* Correct nodes only ever act on messages that actually reached them.
\* Byzantine nodes can conjure anything, so every bundle that is possible
\* from the truth of what was sent is reachable here too.
Recvd(p) == recv[p] \cup {m \in Msgs : \E q \in correct : m \in sent}

\* A correct node emitting an ECHO message to everyone.
Emit(p) ==
    /\ phase[p] # "echo"
    /\ phase' = [phase EXCEPT ![p] = "echo"]
    /\ sent' = sent \cup {<<<<"echo", n>>, p>> : n \in 1 .. N}
    /\ UNCHANGED <<correct, faulty, recv>>

\* Three outcomes: started with INIT and accept immediately, or wait
\* on a quorum of ECHOs before sending and accepting, or just wait.
AcceptSelf(p) ==
    /\ phase[p] \notin {"echo", "accept"}
    /\ Cardinality({m \in Recvd(p) : m[1][1] = "echo"}) >= N - T
    /\ phase' = [phase EXCEPT ![p] = "accept"]
    /\ UNCHANGED <<correct, faulty, recv, sent>>

AcceptNoEcho(p) ==
    /\ phase[p] \notin {"echo", "accept"}
    /\ phase[p] = "init"
    /\ phase' = [phase EXCEPT ![p] = "accept"]
    /\ sent' = sent \cup {<<<<"echo", n>>, p>> : n \in 1 .. N}
    /\ UNCHANGED <<correct, faulty, recv>>

EmitNoEcho(p) ==
    /\ phase[p] \notin {"echo", "accept"}
    /\ phase[p] = "none"
    /\ Cardinality({m \in Recvd(p) : m[1][1] = "echo"}) >= N - 2 * T
    /\ phase[p] # "init"
    /\ Cardinality({m \in Recvd(p) : m[1][1] = "echo"}) < N - T
    /\ sent' = sent \cup {<<<<"echo", n>>, p>> : n \in 1 .. N}
    /\ phase' = [phase EXCEPT ![p] = "echo"]
    /\ UNCHANGED <<correct, faulty, recv>>

Recv(p) ==
    /\ phase[p] \notin {"echo", "accept"}
    /\ recv[p] # Recvd(p)
    /\ recv' = [recv EXCEPT ![p] = Recvd(p)]
    /\ UNCHANGED <<correct, faulty, phase, sent>>

Silent ==
    /\ \E p \in correct : phase[p] \in {"echo", "accept"}
    /\ \A p \in correct : phase[p] = "accept"
    /\ UNCHANGED vars

Step ==
    \/ \E p \in correct : Recv(p) \/ Emit(p) \/ AcceptSelf(p) \/ AcceptNoEcho(p) \/ EmitNoEcho(p)
    \/ Silent

Spec == Init /\ [][Step]_vars
    /\ WF_vars(\E p \in correct : Recv(p))
    /\ WF_vars(\E p \in correct : Emit(p))
    /\ WF_vars(\E p \in correct : AcceptSelf(p))
    /\ WF_vars(\E p \in correct : AcceptNoEcho(p))
    /\ WF_vars(\E p \in correct : EmitNoEcho(p))

TypeOK ==
    /\ correct \subseteq (1 .. N)
    /\ faulty \subseteq (1 .. N)
    /\ phase \in [1 .. N -> Phases]
    /\ recv \in [1 .. N -> SUBSET Msgs]
    /\ sent \subseteq Msgs

FCConstraints ==
    /\ Cardinality(correct) = N - F
    /\ Cardinality(faulty) = F
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

CorrLtl == (\A p \in correct : phase[p] = "init") ~> (\A p \in correct : phase[p] = "accept")
RelayLtl == (\E p \in correct : phase[p] = "accept") ~> (\A p \in correct : phase[p] = "accept")
UnforgLtl == (\A p \in correct : phase[p] = "none") ~> (\A p \in correct : phase[p] = "none")

====