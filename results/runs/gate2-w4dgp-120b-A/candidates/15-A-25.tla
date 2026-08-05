---- MODULE bcastByz ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

\* One-round Asynchronous Reliable Broadcast (Srikanth & Toueg 1987, Fig 7):
\* a correct sender that receives INIT (the "broadcast") echoes to all; a
\* correct receiver accepts once it has collected a quorum of echoes.  Byzantine
\* senders may inject arbitrary ECHO messages.  N > 3T is required for both
\* safety (unforgeability) and correctness.  Two initial states are provided:
\* (a) at least one correct process receives INIT, and (b) no correct process
\* receives INIT -- the latter drives the unforgeability check.

VARIABLES okP, byzP, pc, msgs, sent

vars == <<okP, byzP, pc, msgs, sent>>

Recs == {1..N}
InitA == 1
InitN == 2
EchoS == 3
Accept == 4

Msg == {"ECHO"}

TypeOK ==
  /\ okP \subseteq Recs
  /\ byzP \subseteq Recs
  /\ pc \in [Recs -> {InitA, InitN, EchoS, Accept}]
  /\ msgs \in [Recs -> SUBSET (Recs \X {Msg})]
  /\ sent \subseteq (Recs \X {Msg})

\* No correct participant is ever created or destroyed.
FCConstraints ==
  /\ Cardinality(okP) = N - F
  /\ okP \cap byzP = {}
  /\ okP \cup byzP = Recs

Init ==
  /\ \E G \subseteq Recs :
       /\ Cardinality(G) = N - F
       /\ okP = G
  /\ byzP = Recs \ okP
  /\ pc \in [Recs -> {InitA, InitN}]
  /\ msgs = [p \in Recs |-> {}]
  /\ sent = {}

InitNoBroad ==
  /\ \E G \subseteq Recs :
       /\ Cardinality(G) = N - F
       /\ okP = G
  /\ byzP = Recs \ okP
  /\ pc = [p \in Recs |-> InitN]
  /\ msgs = [p \in Recs |-> {}]
  /\ sent = {}

\* A correct participant may receive a new set of messages (from correct
\* broadcasters and from any Byzantine participant); weak fairness on this
\* and the subsequent actions is what forces progress when a correct
\* participant can keep receiving.
RecvMsgs(p, ne) ==
  /\ pc[p] \in {InitA, InitN, EchoS}
  /\ ne \subseteq (sent \cup (byzP \X {Msg}))
  /\ msgs' = [msgs EXCEPT ![p] = msgs[p] \cup ne]
  /\ UNCHANGED <<okP, byzP, pc, sent>>

\* A correct participant that received the broadcast immediately accepts
\* and sends its single ECHO.
EchoAccept(p) ==
  /\ pc[p] = InitA
  /\ pc' = [pc EXCEPT ![p] = Accept]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<okP, byzP, msgs>>

\* Receiving >= N-2T echoes (but fewer than N-T) is enough to send the
\* echo, but not to accept yet.
EchoProto(p) ==
  /\ pc[p] = InitN
  /\ Cardinality({q \in okP : <<q, "ECHO">> \in msgs[p]}) >= N - 2*T
  /\ Cardinality({q \in okP : <<q, "ECHO">> \in msgs[p]}) < N - T
  /\ pc' = [pc EXCEPT ![p] = EchoS]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<okP, byzP, msgs>>

\* Receiving >= N-T echoes forces both the echo and immediate acceptance.
EchoAcceptProto(p) ==
  /\ pc[p] = InitN
  /\ Cardinality({q \in okP : <<q, "ECHO">> \in msgs[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = Accept]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<okP, byzP, msgs>>

\* Having already sent an echo, a correct participant accepts once it
\* reaches the tighter N-T quorum.
AcceptProto(p) ==
  /\ pc[p] = EchoS
  /\ Cardinality({q \in okP : <<q, "ECHO">> \in msgs[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = Accept]
  /\ UNCHANGED <<okP, byzP, msgs, sent>>

Next ==
  \/ \E p \in Recs, ne \in SUBSET (Recs \X {Msg}) : RecvMsgs(p, ne)
  \/ \E p \in okP : EchoAccept(p)
  \/ \E p \in okP : EchoProto(p)
  \/ \E p \in okP : EchoAcceptProto(p)
  \/ \E p \in okP : AcceptProto(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Recs, ne \in SUBSET (Recs \X {Msg}) : RecvMsgs(p, ne))
  /\ WF_vars(\E p \in okP : EchoProto(p))
  /\ WF_vars(\E p \in okP : EchoAcceptProto(p))

SpecNoBroad ==
  /\ InitNoBroad
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Recs, ne \in SUBSET (Recs \X {Msg}) : RecvMsgs(p, ne))
  /\ WF_vars(\E p \in okP : EchoProto(p))
  /\ WF_vars(\E p \in okP : EchoAcceptProto(p))

\* Unforgeability: if no correct participant broadcasts, none can ever
\* accept, so no forged (unauthorized) acceptance ever occurs.
UnforgLtl == (N - F >= 1) ~> (N - F < 1) ~> (\A p \in okP : pc[p] # Accept)

CorrLtl ==
  /\ (\A p \in okP : pc[p] = InitA) ~> (\A p \in okP : pc[p] = Accept)
  /\ (\E p \in okP : pc[p] = InitA) ~> (\A p \in okP : pc[p] = InitA)

RelayLtl ==
  (\E p \in okP : pc[p] = Accept) ~> (\A p \in okP : pc[p] = Accept)

====