---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, recv, sent

vars == << correct, faulty, pc, recv, sent >>

States == {"noInit", "hasInit", "echoSent", "accepted"}

\* A message is just an (sender, type) pair; the protocol only ever sends ECHO.
Msg == [snd : 1..N, typ : {"ECHO"}]

TypeOK ==
    /\ correct \subseteq (1..N)
    /\ faulty \subseteq (1..N)
    /\ pc \in [1..N -> States]
    /\ recv \in [1..N -> SUBSET Msg]
    /\ sent \subseteq Msg

Init ==
    /\ correct = CHOOSE S \in SUBSET (1..N) : Cardinality(S) = (N - F)
    /\ faulty = (1..N) \ correct
    /\ pc = [p \in 1..N |-> IF p \in correct THEN "noInit" ELSE "noInit"]
    /\ recv = [p \in 1..N |-> {}]
    /\ sent = {}

\* A correct process may receive a batch of messages from correct senders and
\* any messages from Byzantine processes together, nondeterministically.
Receive(p) ==
    /\ pc[p] \in {"noInit", "hasInit"}
    /\ recv' = [recv EXCEPT ![p] =
            recv[p] \union
                {m \in (sent \cup [snd |-> q \in faulty, typ |-> "ECHO"])
                     : ~ \E x \in recv[p] : x.snd = m.snd /\ x.typ = m.typ}]
    /\ UNCHANGED << correct, faulty, sent, pc >>

\* A correct process with INIT sends ECHO and accepts immediately.
Broadcast(p) ==
    /\ pc[p] = "hasInit"
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ sent' = sent \union {[snd |-> p, typ |-> "ECHO"]}
    /\ UNCHANGED << correct, faulty, recv >>

\* Distinct senders needed to keep Byzantine messaging from forging acceptance.
RelayEcho(p) ==
    /\ pc[p] = "noInit"
    /\ Cardinality({m.snd : m \in recv[p] /\ m.typ = "ECHO"}) >= (N - 2 * T)
    /\ Cardinality({m.snd : m \in recv[p] /\ m.typ = "ECHO"}) < (N - T)
    /\ pc' = [pc EXCEPT ![p] = "echoSent"]
    /\ sent' = sent \union {[snd |-> p, typ |-> "ECHO"]}
    /\ UNCHANGED << correct, faulty, recv >>

RelayAccept(p) ==
    /\ pc[p] \in {"noInit", "echoSent"}
    /\ Cardinality({m.snd : m \in recv[p] /\ m.typ = "ECHO"}) >= (N - T)
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ sent' = sent \union {[snd |-> p, typ |-> "ECHO"]}
    /\ UNCHANGED << correct, faulty, recv >>

Accept(p) ==
    /\ pc[p] = "echoSent"
    /\ Cardinality({m.snd : m \in recv[p] /\ m.typ = "ECHO"}) >= (N - T)
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED << correct, faulty, recv, sent >>

Next ==
    \/ \E p \in 1..N : Receive(p)
    \/ \E p \in correct : Broadcast(p)
    \/ \E p \in correct : RelayEcho(p)
    \/ \E p \in correct : RelayAccept(p)
    \/ \E p \in correct : Accept(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in correct : Receive(p))
    /\ WF_vars(\E p \in correct : Broadcast(p) \/ RelayEcho(p) \/ RelayAccept(p) \/ Accept(p))

\* If no correct process ever broadcast, none may ever accept.
UnforgLtl == (\A p \in correct : pc[p] # "hasInit") ~> (\A p \in correct : pc[p] # "accepted")

CorrLtl == (\A p \in correct : pc[p] = "hasInit") ~> (\A p \in correct : pc[p] = "accepted")
RelayLtl == (\E p \in correct : pc[p] = "accepted") ~> (\A p \in correct : pc[p] = "accepted")

\* Correctness rests on the same cardinality bound as the acceptance property itself.
FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

====