---- MODULE bcastByz ----
(***************************************************************************)
(* Srikanth & Toueg 1987: one-round asynchronous reliable broadcast.      *)
(* This is a parameterized model with Byzantine senders.  Correct processes *)
(* follow the protocol; Byzantine processes may send arbitrary ECHO messages. *)
(* Strong safety: if no correct process ever broadcasts (no INIT), no       *)
(* correct process ever accepts.                                            *)
(* Strong liveness: if all correct processes start with the INIT message,   *)
(* then all correct processes eventually accept.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME N > 3 * T
ASSUME T >= F
ASSUME F >= 0

Procs == 1..N
Byz == 1..F
Correct == {p \in Procs : p > F}

\* Each correct process starts in one of two states: 0 = no INIT, 1 = INIT.
InitState == 0 \cup 1

\* Protocol states: 0=not received INIT, 1=received INIT, 2=sent ECHO, 3=accepted.
State == 0 \cup 1 \cup 2 \cup 3

\* Messages are ECHO messages tagged with the sender identity.
Msg == [sender : Procs, type : {"ECHO"}]

\* The set of messages that have been sent by correct processes.
SentByCorrect == SUBSET (Correct \X {"ECHO"})

\* The set of messages that have been received by each process.
\* For a correct process p, Recv[p] is the set of messages it has received.
Recv == [p \in Procs |-> SUBSET Msg]

Init == /\ Procs = DOMAIN Recv
        /\ \A p \in Procs : Recv[p] = {}
        /\ \A p \in Procs : p \in Correct => p \in InitState
        /\ \A p \in Procs : p \in Byz => p \notin InitState
        /\ SentByCorrect = {}

\* A correct process that has received the INIT message immediately sends an
\* ECHO to all (this is the "broadcast" step of the protocol).
SendEcho(p) ==
    /\ p \in Correct
    /\ p \in InitState
    /\ p \notin SentByCorrect
    /\ SentByCorrect' = SentByCorrect \cup {p}
    /\ UNCHANGED Recv

\* A correct process may receive any subset of the messages that have been
\* sent by correct processes (and any arbitrary ECHO from a Byzantine sender).
\* This models the asynchronous message delivery and Byzantine senders.
RecvMsg(p, m) ==
    /\ p \in Procs
    /\ m \in (SentByCorrect \X {"ECHO"}) \cup (Byz \X {"ECHO"})
    /\ m \notin Recv[p]
    /\ Recv' = [Recv EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED SentByCorrect

\* A correct process that has not yet sent its ECHO may send it once it has
\* received at least N-2T ECHO messages from distinct senders but fewer than
\* N-T.  It does not yet accept.
SendEchoIfThreshold(p) ==
    /\ p \in Correct
    /\ p \notin SentByCorrect
    /\ Cardinality({ m \in Recv[p] : m.type = "ECHO" }) >= N - 2 * T
    /\ Cardinality({ m \in Recv[p] : m.type = "ECHO" }) < N - T
    /\ SentByCorrect' = SentByCorrect \cup {p}
    /\ UNCHANGED Recv

\* A correct process that has not yet sent its ECHO may send it once it has
\* received at least N-T ECHO messages from distinct senders.  It immediately
\* accepts.
SendEchoAndAccept(p) ==
    /\ p \in Correct
    /\ p \notin SentByCorrect
    /\ Cardinality({ m \in Recv[p] : m.type = "ECHO" }) >= N - T
    /\ SentByCorrect' = SentByCorrect \cup {p}
    /\ UNCHANGED Recv

\* A correct process that has already sent its ECHO may accept once it has
\* received at least N-T ECHO messages from distinct senders.
AcceptIfThreshold(p) ==
    /\ p \in Correct
    /\ p \in SentByCorrect
    /\ Cardinality({ m \in Recv[p] : m.type = "ECHO" }) >= N - T
    /\ UNCHANGED SentByCorrect
    /\ UNCHANGED Recv

Next == \/ \E p \in Procs : SendEcho(p)
        \/ \E p \in Procs : RecvMsg(p, [sender |-> p, type |-> "ECHO"])
        \/ \E p \in Procs : SendEchoIfThreshold(p)
        \/ \E p \in Procs : SendEchoAndAccept(p)
        \/ \E p \in Procs : AcceptIfThreshold(p)

Spec == Init /\ [][Next]_<<Recv, SentByCorrect>>

\* Strong safety: if no correct process ever broadcasts (no INIT), no correct
\* process ever accepts.
UnforgLtl == [](~(F = 0) => ~(\E p \in Correct : p \in SentByCorrect))

\* Strong liveness: if all correct processes start with the INIT message,
\* then eventually all correct processes accept.
CorrLtl == [](~(F = 0) => <> (\A p \in Correct : p \in SentByCorrect))

\* Relay: if any correct process accepts, then eventually all correct
\* processes accept.
RelayLtl == (\E p \in Correct : p \in SentByCorrect) => <> (\A p \in Correct : p \in SentByCorrect)

TypeOK ==
    /\ Recv \in [Procs -> SUBSET Msg]
    /\ SentByCorrect \subseteq Correct

FCConstraints == /\ Cardinality(Correct) = N - F
                 /\ Cardinality(Byz) = F
====