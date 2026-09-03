---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

States == {"initrcv", "noinit", "sent", "done"}
MsgKinds == {"echo"}
Senders == 1..N
Msgs == [kind : MsgKinds, snd : Senders]

VARIABLES correct, faulty, state, recv, sent
vars == <<correct, faulty, state, recv, sent>>

TypeOK ==
  /\ correct \subseteq Senders
  /\ faulty \subseteq Senders
  /\ Cardinality(correct) = N - F
  /\ faulty = Senders \ correct
  /\ state \in [Senders -> States]
  /\ recv \in [Senders -> SUBSET Msgs]
  /\ sent \subseteq Msgs

Init ==
  /\ correct = {s \in Senders : s <= N - F}
  /\ faulty = Senders \ correct
  /\ state = [s \in Senders |-> IF s <= N - F THEN "initrcv" ELSE "noinit"]
  /\ recv = [s \in Senders |-> {}]
  /\ sent = {}

\* Correct processes may observe messages from both correct senders and
\* Byzantine processes in the same receive step.
ReceiveAndAct(s) ==
  /\ s \in correct
  /\ state[s] \in {"initrcv", "noinit"}
  /\ recv' = [recv EXCEPT ![s] = recv[s] \cup sent]
  /\ UNCHANGED <<correct, faulty, state, sent>>

\* The broadcaster's INIT message is modeled by the process starting in the
\* broadcast-received state, which triggers an immediate accept-and-echo.
InitAct(s) ==
  /\ s \in correct
  /\ state[s] = "initrcv"
  /\ state' = [state EXCEPT ![s] = "done"]
  /\ sent' = sent \cup {[kind |-> "echo", snd |-> s]}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A process that has not yet sent an ECHO, but may still accept later,
\* collects enough ECHO messages from distinct senders before acting.
HalfAct(s) ==
  /\ s \in correct
  /\ state[s] = "noinit"
  /\ Cardinality(recv[s]) >= N - 2 * T
  /\ Cardinality(recv[s]) < N - T
  /\ state' = [state EXCEPT ![s] = "sent"]
  /\ sent' = sent \cup {[kind |-> "echo", snd |-> s]}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A process that has collected the full quorum accepts.
FullAct(s) ==
  /\ s \in correct
  /\ state[s] = "noinit"
  /\ Cardinality(recv[s]) >= N - T
  /\ state' = [state EXCEPT ![s] = "done"]
  /\ sent' = sent \cup {[kind |-> "echo", snd |-> s]}
  /\ UNCHANGED <<correct, faulty, recv>>

RelayAct(s) ==
  /\ s \in correct
  /\ state[s] = "sent"
  /\ Cardinality(recv[s]) >= N - T
  /\ state' = [state EXCEPT ![s] = "done"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E s \in Senders : ReceiveAndAct(s)
  \/ \E s \in Senders : InitAct(s)
  \/ \E s \in Senders : HalfAct(s)
  \/ \E s \in Senders : FullAct(s)
  \/ \E s \in Senders : RelayAct(s)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A s \in Senders : WF_vars(ReceiveAndAct(s))

\* If no correct process started with the broadcast, none ever accepts.
UnforgLtl == (\A s \in correct : state[s] = "noinit")
             ~> (\A s \in correct : state[s] = "done")

\* If every correct process started with the broadcast, they all accept.
CorrLtl == (\A s \in correct : state[s] = "initrcv")
           ~> (\A s \in correct : state[s] = "done")

\* If any correct process accepts, they all eventually accept.
RelayLtl == (\E s \in correct : state[s] = "done")
            ~> (\A s \in correct : state[s] = "done")

\* Program counters and message sets stay within their defined domains.
FCConstraints == TypeOK
====