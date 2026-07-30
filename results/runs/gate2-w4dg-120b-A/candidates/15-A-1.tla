---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES corrects, faulty, pc, recv, mbuf
vars == <<corrects, faulty, pc, recv, mbuf>>

RECURSIVE Distinct(_)
Distinct(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN 1 + Distinct(S \ {x})

InitState == [pc |-> "spont", recv |-> {}, mbuf |-> {}]

TypeOK ==
  /\ corrects \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> {"spont", "wait", "sent", "done"}]
  /\ recv \in [1..N -> SUBSET [snd : 1..N, tp : {"init", "echo"}]]
  /\ mbuf \subseteq [snd : 1..N, tp : {"init", "echo"}]

Init ==
  /\ Cardinality(corrects) = N - F
  /\ faulty = (1..N) \ corrects
  /\ \A p \in 1..N :
       \/ (p \in corrects /\ pc[p] = "wait")
       \/ (p \in corrects /\ pc[p] = "spont")
       \/ (p \in faulty /\ pc[p] = "spont")
  /\ UNCHANGED <<recv, mbuf>>

\* Correct processes may receive any mix of correct and Byzantine messages.
Recv(p, S) ==
  /\ p \in corrects
  /\ S \subseteq mbuf
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup S]
  /\ UNCHANGED <<corrects, faulty, pc, mbuf>>

\* A correct process that received the broadcaster's INIT message accepts and
\* echoes immediately.
ActOnInit(p) ==
  /\ p \in corrects
  /\ pc[p] = "wait"
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ mbuf' = mbuf \cup {[snd |-> p, tp |-> "echo"]}
  /\ UNCHANGED <<corrects, faulty, recv>>

\* A correct process that has not yet echoed may forward once it has collected a
\* strong-but-not-quorum majority.
EchoStrong(p) ==
  /\ p \in corrects
  /\ pc[p] = "spont"
  /\ Distinct({m.snd : m \in recv[p]}) >= N - 2 * T
  /\ Distinct({m.snd : m \in recv[p]}) < N - T
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ mbuf' = mbuf \cup {[snd |-> p, tp |-> "echo"]}
  /\ UNCHANGED <<corrects, faulty, recv>>

\* A correct process that has not yet echoed accepts once it has a quorum.
EchoQuorum(p) ==
  /\ p \in corrects
  /\ pc[p] = "spont"
  /\ Distinct({m.snd : m \in recv[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ mbuf' = mbuf \cup {[snd |-> p, tp |-> "echo"]}
  /\ UNCHANGED <<corrects, faulty, recv>>

\* A correct process that has already echoed accepts when it collects a quorum.
Accept(p) ==
  /\ p \in corrects
  /\ pc[p] \in {"spont", "sent"}
  /\ Distinct({m.snd : m \in recv[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<corrects, faulty, recv, mbuf>>

\* A correct process can never act without messages from a majority of correct
\* senders: once at most T processes remain silent, every correct process must
\* accept.
QuorumBound ==
  \A p \in corrects : pc[p] = "done" => Distinct({m.snd : m \in recv[p]}) >= N - T

Next ==
  \/ \E p \in 1..N, S \in SUBSET [snd : 1..N, tp : {"init", "echo"}] : Recv(p, S)
  \/ \E p \in 1..N : ActOnInit(p)
  \/ \E p \in 1..N : EchoStrong(p)
  \/ \E p \in 1..N : EchoQuorum(p)
  \/ \E p \in 1..N : Accept(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in corrects : WF_vars(\E S \in SUBSET [snd : 1..N, tp : {"init", "echo"}] : Recv(p, S))

\* A correct process may accept only through the forward-and-accept path once it
\* has collected a quorum of ECHO messages; without a quorum it can never accept.
CorrLtl == \A p \in corrects : (pc[p] = "done") ~> (Distinct({m.snd : m \in recv[p]}) >= N - T)

\* If one correct participant accepts, all must accept.
RelayLtl == (\E p \in corrects : pc[p] = "done") ~> (\A p \in corrects : pc[p] = "done")

\* If no correct process broadcast the INIT message, none ever accepts.
UnforgLtl == (\A p \in corrects : pc[p] = "spont") ~> (\A p \in corrects : pc[p] # "done")

FCConstraints == QuorumBound
====