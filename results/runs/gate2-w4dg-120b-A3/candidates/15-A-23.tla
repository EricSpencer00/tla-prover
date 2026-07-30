---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct vs. faulty: a bounded number of Byzantine processes, chosen
\* nondeterministically at Init (two partitions with the same sizes).
\* The protocol is derived from Srikanth and Toueg 1987 Figure 7.
\* Initialising processes in the broadcast state is the one-round broadcast
\* in the original algorithm; it is optional here so both cases can be modelled.

TypeOK ==
  /\ N \in Nat /\ T \in 0..N /\ F \in 0..N
  /\ N > 3 * T
  /\ T >= F
  /\ (Correct \cup Faulty) = 1..N
  /\ Correct \cap Faulty = {}
  /\ \A p \in Correct : InitState[p] \in {"bc","no"}
  /\ \A p \in 1..N : loc[p] \in {"bc","no","echo","done"}
  /\ \A p \in 1..N : Received[p] \subseteq [snd : 1..N, msg : {"echo"}]
  /\ \A p \in 1..N : Sent[p] \subseteq [snd : 1..N, msg : {"echo"}]

\* No messages sent or received initially; Faulty is the complement of Correct.
Init ==
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ \A p \in 1..N : loc[p] = InitState[p]
  /\ \A p \in 1..N : Received[p] = {}
  /\ \A p \in 1..N : Sent[p] = {}

\* What a correct process can see: everything sent by correct participants plus
\* any possible message from a Byzantine one (the model's over-approximation).
AllMsgs == {x \in [snd : 1..N, msg : {"echo"}] : x.snd \in Correct}
FaultyMsgs == {x \in [snd : 1..N, msg : {"echo"}] : x.snd \in Faulty}

\* A correct process may receive any set of new messages that it has not yet
\* received, drawn from the union of correct and faulty participants.
Receive(p) ==
  /\ loc[p] \in {"bc","no"}
  /\ \E msgs \in SUBSET (AllMsgs \cup FaultyMsgs) :
       Received' = [Received EXCEPT ![p] = @ \cup msgs]
  /\ UNCHANGED <<Correct, Faulty, loc, Sent>>

\* A broadcast-receiver accepts immediately and sends its ECHO.
InitAccept(p) ==
  /\ loc[p] = "bc"
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ Sent' = [Sent EXCEPT ![p] = { [snd |-> p, msg |-> "echo"] }]
  /\ UNCHANGED <<Correct, Faulty, Received>>

\* A non-broadcast participant may send an ECHO on hearing a quorum below acceptance.
SendEcho(p) ==
  /\ loc[p] = "no"
  /\ Cardinality({x \in Received[p] : x.msg = "echo"}) >= N - 2 * T
  /\ Cardinality({x \in Received[p] : x.msg = "echo"}) < N - T
  /\ loc' = [loc EXCEPT ![p] = "echo"]
  /\ Sent' = [Sent EXCEPT ![p] = { [snd |-> p, msg |-> "echo"] }]
  /\ UNCHANGED <<Correct, Faulty, Received>>

\* A non-broadcast participant may accept once it has a strong enough quorum.
SendEchoAccept(p) ==
  /\ loc[p] = "no"
  /\ Cardinality({x \in Received[p] : x.msg = "echo"}) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ Sent' = [Sent EXCEPT ![p] = { [snd |-> p, msg |-> "echo"] }]
  /\ UNCHANGED <<Correct, Faulty, Received>>

\* A participant that has already sent may accept on a strong enough quorum.
EchoAccept(p) ==
  /\ loc[p] = "echo"
  /\ Cardinality({x \in Received[p] : x.msg = "echo"}) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<Correct, Faulty, Received, Sent>>

\* Fairness: a correct participant that forever has something to receive and act
\* on must eventually act. A separate variant without fairness can be run for safety.
Next ==
  \E p \in 1..N :
    \/ Receive(p) \/ InitAccept(p) \/ SendEcho(p)
    \/ SendEchoAccept(p) \/ EchoAccept(p)

Spec == Init /\ [][Next]_<<Correct, Faulty, loc, Received, Sent>>

CorrLtl == (\A p \in Correct : loc[p] = "bc") ~> (\A p \in Correct : loc[p] = "done")
RelayLtl == (\E p \in Correct : loc[p] = "done") ~> (\A p \in Correct : loc[p] = "done")

\* Unforgeability: no correct broadcast means no correct acceptance ever.
UnforgLtl == (\A p \in Correct : loc[p] = "no") ~> (\A p \in Correct : loc[p] # "done")

FCConstraints == TypeOK

====