---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc          \* Set of process identifiers
          d0            \* Default timeout value (positive integer)
          SendPoint     \* Send interval (positive integer, not a multiple of PredictPoint)
          PredictPoint  \* Predict interval (positive integer, not a multiple of SendPoint)
          Messages      \* Set of message identifiers (one per process)

\* Derived constants for convenience
\* All processes to which a given process can send messages (including itself)
AllProcs == Proc

\* Type synonym for clarity
Msg == [sender : Proc]

VARIABLES
    suspicion,          \* [p \in Proc -> SUBSET Proc]
    timeout,            \* [p \in Proc -> [q \in Proc -> Nat]]   \* adaptive timeout intervals
    lastHeard,          \* [p \in Proc -> [q \in Proc -> Nat]]   \* counters since last heard
    clock,              \* [p \in Proc -> Nat]
    outMsgSet           \* [p \in Proc -> SUBSET Msg]           \* outgoing messages awaiting send

\* --------------------------------------------------------------------------
\* Type invariant (optional, but part of the required INVARIANT)
\* --------------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outMsgSet \in [Proc -> SUBSET Msg]
    /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
    /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat]
    /\ \A p \in Proc : outMsgSet[p] \subseteq { [sender |-> q] : q \in Proc }

\* --------------------------------------------------------------------------
\* Initial state
\* --------------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outMsgSet = [p \in Proc |-> {}]

\* --------------------------------------------------------------------------
\* Helper definitions
\* --------------------------------------------------------------------------
SendTrigger(p)   == clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0
PredictTrigger(p) == clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0
\* The modulo operations ensure send and predict never coincide

\* --------------------------------------------------------------------------
\* Actions
\* --------------------------------------------------------------------------
SendAlive(p) ==
    /\ SendTrigger(p)
    /\ \E m \in Messages :
          \E to \in Proc :
              /\ m = [sender |-> p]
              /\ outMsgSet' = [outMsgSet EXCEPT ![p] = outMsgSet[p] \cup {m}]
              /\ /\ lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1
                                  FOR q \in Proc]
               /\ /\ clock' = [clock EXCEPT ![p] = (clock[p] + 1) % (SendPoint + PredictPoint)]
               /\ /\ UNCHANGED << suspicion, timeout >>
    \/ /\ clock' = [clock EXCEPT ![p] = (clock[p] + 1) % (SendPoint + PredictPoint)]
       /\ UNCHANGED << suspicion, timeout, lastHeard, outMsgSet >>

Predict(p) ==
    /\ PredictTrigger(p)
    /\ /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup
                        {q \in Proc : lastHeard[p][q] >= timeout[p][q]}]
       /\ /\ clock' = [clock EXCEPT ![p] = (clock[p] + 1) % (SendPoint + PredictPoint)]
       /\ /\ UNCHANGED << timeout, lastHeard, outMsgSet >>

Receive(p) ==
    /\ \A q \in Proc :
          /\ \E m \in outMsgSet[q] : m.sender = q
          /\ /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
             /\ /\ timeout' = [timeout EXCEPT ![p][q] = timeout[p][q] + 1]
          /\ /\ outMsgSet' = [outMsgSet EXCEPT ![q] = outMsgSet[q] \ {m}]
          /\ /\ clock' = [clock EXCEPT ![p] = (clock[p] + 1) % (SendPoint + PredictPoint)]
          /\ /\ UNCHANGED << suspicion >>
       \/ /\ /\ UNCHANGED << suspicion, timeout, lastHeard, outMsgSet >>
           /\ clock' = [clock EXCEPT ![p] = (clock[p] + 1) % (SendPoint + PredictPoint)]

\* --------------------------------------------------------------------------
\* Next-state relation
\* --------------------------------------------------------------------------
Next ==
    \E p \in Proc :
          \/ SendAlive(p)
          \/ Predict(p)
          \/ Receive(p)

\* --------------------------------------------------------------------------
\* Specification
\* --------------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_ << suspicion, timeout, lastHeard, clock, outMsgSet >>

====