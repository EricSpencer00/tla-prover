---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct broadcast with Byzantine faults, one-round async reliable broadcast
\* from Srikanth & Toueg 1987 Fig.7, modelled as INIT-received vs not-at-start.
\* Two initial states: unrestricted (any partition, any broadcast set) and
\* restricted (no correct process broadcast), the latter used to check safety.
\* Weak fairness drives the reliable-delivery step for a correct process.

MessageTypes == {"ECHO"}

VARIABLES correct, faulty, phase, inbox, sentMsgs

vars == <<correct, faulty, phase, inbox, sentMsgs>>

RECURSIVE From(_, _)
From(S, f) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE IN {f[x]} \cup From(S \ {x}, f)

\* At most one ECHO per sender counts toward the quorum.
EchoSenders(p) == {m.sender : m \in inbox[p]}

InitState == [p \in 1..N |-> IF p = 1 THEN "hasInit" ELSE "noInit"]

TypeOK ==
    /\ correct \subseteq (1..N) /\ faulty \subseteq (1..N)
    /\ correct \cap faulty = {} /\ correct \cup faulty = (1..N)
    /\ phase \in [1..N -> {"hasInit", "noInit", "sentEcho", "accepted"}]
    /\ inbox \in [1..N -> SUBSET [sender : 1..N, kind : MessageTypes]]
    /\ sentMsgs \in SUBSET [sender : 1..N, kind : MessageTypes]

\* Unforgeability: without a correct broadcast, no correct process accepts.
FCConstraints ==
    /\ N \in (3 * (T + 1))..Nat
    /\ T \in (F)..(N - 1)
    /\ F \in 0..T

Init ==
    /\ \E C \in {S \in SUBSET (1..N) : Cardinality(S) = N - F}
       correct = C /\ faulty = (1..N) \ C
    /\ phase = InitState
    /\ sentMsgs = {}
    /\ inbox = [p \in 1..N |-> {}]

\* Over-approximate receive: a correct process may pick any non-empty set of
\* messages from correct senders and any set of messages from Byzantine
\* senders (the adversary) in one step, then act on it immediately.
ReceiveAndAct ==
    \E p \in correct :
        /\ \E m \in (From(correct, [sender |-> #, kind |-> "ECHO"]) \cup
                     From(faulty, [sender |-> #, kind |-> "ECHO"])) \ {}
             : inbox' = [inbox EXCEPT ![p] = @ \cup m]
        /\ \E k \in [sender : 1..N, kind : MessageTypes] : sentMsgs' = sentMsgs \cup {k}
        /\ IF phase[p] = "hasInit"
             THEN phase' = [phase EXCEPT ![p] = "accepted"]
             ELSE IF phase[p] \in {"noInit", "sentEcho"} /\ Cardinality(EchoSenders(p)) >= N - 2 * T
                     /\ Cardinality(EchoSenders(p)) < N - T
                  THEN phase' = [phase EXCEPT ![p] = "sentEcho"]
                  ELSE IF phase[p] \in {"noInit", "sentEcho"} /\ Cardinality(EchoSenders(p)) >= N - T
                       THEN phase' = [phase EXCEPT ![p] = "accepted"]
                       ELSE IF phase[p] = "sentEcho" /\ Cardinality(EchoSenders(p)) >= N - T
                            THEN phase' = [phase EXCEPT ![p] = "accepted"]
                            ELSE phase
        /\ UNCHANGED <<correct, faulty>>

NoAction == UNCHANGED vars

Next == ReceiveAndAct \/ NoAction

Fairness ==
    /\ WF_vars(ReceiveAndAct)
    /\ SF_vars(NoAction)

Spec == Init /\ [][Next]_vars
LivenessSpec == Fairness /\ Init

CorrLtl == (correct = (1..N) => <>(\A p \in correct : phase[p] = "accepted"))
RelayLtl == (\E p \in correct : phase[p] = "accepted") ~> (\A p \in correct : phase[p] = "accepted")
UnforgLtl == (1 \notin correct) => (\A p \in correct : phase[p] # "accepted")

====