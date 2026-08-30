---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A process either received the broadcaster's INIT message or it did not;
\* this is the per-process record of whether INIT was ever broadcast.
VARIABLES correct, faulty, pc, rcvd, sent

vars == <<correct, faulty, pc, rcvd, sent>>

PcStates == {"nobrcv", "rcvd", "sent", "accept"}

InitStates == {"nobrcv", "rcvd"}

TypeOK ==
    /\ correct \subseteq 1..N
    /\ faulty \subseteq 1..N
    /\ pc \in [1..N -> PcStates]
    /\ rcvd \in [1..N -> SUBSET (1..N \X {"echo"})]
    /\ sent \subseteq (1..N \X {"echo"})

\* The safety invariant is unforgeability (no accept on no broadcast); the
\* domain-compliance checks are collected under TypeOK.
Unforgeability ==
    \A i \in correct : (pc[i] = "accept") => (i \in faulty \/ InitStates = {"rcvd"})

CorrLtl == <>(\A i \in correct : pc[i] = "accept")

RelayLtl == (\E i \in correct : pc[i] = "accept") ~> (\A i \in correct : pc[i] = "accept")

FCConstraints == UNCHANGED <<correct, faulty, pc, rcvd, sent>>

Init ==
    /\ correct = {1..(N - F)}
    /\ faulty = 1..N \ correct
    /\ pc = [i \in 1..N |-> InitStates @@ ((N - F) % 2 + 1)]
    /\ rcvd = [i \in 1..N |-> {}]
    /\ sent = {}

RestrictedInit ==
    /\ correct = {1..(N - F)}
    /\ faulty = 1..N \ correct
    /\ pc = [i \in 1..N |-> "nobrcv"]
    /\ rcvd = [i \in 1..N |-> {}]
    /\ sent = {}

\* Correct receivers only; a Byzantine can forge any sender/value pair.
Receive(i) ==
    /\ i \in correct
    /\ pc[i] \in {"nobrcv", "rcvd"}
    /\ rcvd' = [rcvd EXCEPT ![i] = rcvd[i] \cup
                    {m \in sent : (m[2] = "echo") /\ m[1] \in correct}]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

\* Strongly fast path: receiving INIT means acceptance without a quorum.
AcceptOnInit(i) ==
    /\ i \in correct
    /\ pc[i] = "rcvd"
    /\ pc' = [pc EXCEPT ![i] = "accept"]
    /\ sent' = sent \cup {<<i, "echo">>}
    /\ UNCHANGED <<correct, faulty, rcvd>>

SendEcho(i) ==
    /\ i \in correct
    /\ pc[i] \in {"nobrcv", "rcvd"}
    /\ Cardinality(rcvd[i]) >= (N - 2 * T)
    /\ Cardinality(rcvd[i]) < (N - T)
    /\ sent' = sent \cup {<<i, "echo">>}
    /\ pc' = [pc EXCEPT ![i] = "sent"]
    /\ UNCHANGED <<correct, faulty, rcvd>>

AcceptOnQuorum(i) ==
    /\ i \in correct
    /\ pc[i] \in {"nobrcv", "rcvd"}
    /\ Cardinality(rcvd[i]) >= (N - T)
    /\ sent' = sent \cup {<<i, "echo">>}
    /\ pc' = [pc EXCEPT ![i] = "accept"]
    /\ UNCHANGED <<correct, faulty, rcvd>>

AcceptOnEcho(i) ==
    /\ i \in correct
    /\ pc[i] = "sent"
    /\ Cardinality(rcvd[i]) >= (N - T)
    /\ pc' = [pc EXCEPT ![i] = "accept"]
    /\ UNCHANGED <<correct, faulty, rcvd, sent>>

Next ==
    \/ \E i \in 1..N : Receive(i)
    \/ \E i \in 1..N : AcceptOnInit(i)
    \/ \E i \in 1..N : SendEcho(i)
    \/ \E i \in 1..N : AcceptOnQuorum(i)
    \/ \E i \in 1..N : AcceptOnEcho(i)
    \/ FCConstraints

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E i \in 1..N : AcceptOnInit(i))
    /\ WF_vars(\E i \in 1..N : SendEcho(i))
    /\ WF_vars(\E i \in 1..N : AcceptOnQuorum(i))

UnforgLtl == Unforgeability

====