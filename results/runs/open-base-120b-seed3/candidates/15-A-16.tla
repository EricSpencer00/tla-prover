---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, received, sent

\* ----------------------------------------------------------------------
\* Message definition (only ECHO messages)
\* ----------------------------------------------------------------------
Msg == [type : {"ECHO"}, sender : 1..N]

MsgSet == { [type |-> "ECHO", sender |-> s] : s \in 1..N }

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(p) == { m.sender : m \in received[p] /\ m.type = "ECHO" }

Count(p) == Cardinality(EchoSenders(p))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq 1..N
  /\ Cardinality(Correct) = N - F
  /\ Faulty = 1..N \ Correct
  /\ \E initMap \in [Correct -> {"InitRec", "NoInit"}] :
        /\ pc = [i \in 1..N |-> IF i \in Correct THEN initMap[i] ELSE "Byz"]
        /\ received = [i \in 1..N |-> {}]
        /\ sent = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Receive new messages (including arbitrary Byzantine messages)
Receive(p) ==
  /\ p \in Correct
  /\ \E new \subseteq (sent \cup MsgSet) :
        /\ received' = [received EXCEPT ![p] = received[p] \cup new]
        /\ UNCHANGED <<Correct, Faulty, pc, sent>>

\* Send ECHO only (do not accept yet) – triggered when count >= N-2T but < N-T
SendEchoOnly(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ Count(p) >= N - 2 * T
  /\ Count(p) < N - T
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
  /\ UNCHANGED <<Correct, Faulty, received>>

\* Send ECHO and accept (covers InitRec case and count >= N-T)
SendEchoAndAccept(p) ==
  /\ p \in Correct
  /\ pc[p] \in {"InitRec", "NoInit"}
  /\ (pc[p] = "InitRec" \/ Count(p) >= N - T)
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, received>>

\* Accept without sending (already sent ECHO)
AcceptOnly(p) ==
  /\ p \in Correct
  /\ pc[p] = "EchoSent"
  /\ Count(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, received, sent>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Correct: Receive(p)
  \/ \E p \in Correct: SendEchoOnly(p)
  \/ \E p \in Correct: SendEchoAndAccept(p)
  \/ \E p \in Correct: AcceptOnly(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Correct, Faulty, pc, received, sent>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq 1..N
  /\ Cardinality(Correct) = N - F
  /\ Faulty = 1..N \ Correct
  /\ pc \in [1..N -> {"NoInit","InitRec","EchoSent","Accepted","Byz"}]
  /\ \A i \in 1..N :
        IF i \in Correct THEN pc[i] \in {"NoInit","InitRec","EchoSent","Accepted"}
        ELSE pc[i] = "Byz"
  /\ received \in [1..N -> SUBSET MsgSet]
  /\ sent \in SUBSET MsgSet
  /\ \A m \in sent: m.type = "ECHO" /\ m.sender \in 1..N
  /\ \A i \in 1..N: \A m \in received[i]: m.type = "ECHO" /\ m.sender \in 1..N

\* ----------------------------------------------------------------------
\* Fault‑tolerance constraints (from the description)
\* ----------------------------------------------------------------------
FCConstraints == 
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl ==
  [] ( (\A p \in Correct: pc[p] = "InitRec") => <> ( /\A p \in Correct: pc[p] = "Accepted") )

RelayLtl ==
  [] ( (\E p \in Correct: pc[p] = "Accepted") => <> ( /\A p \in Correct: pc[p] = "Accepted") )

UnforgLtl ==
  [] ( (\A p \in Correct: pc[p] = "NoInit") => [] ( /\A p \in Correct: pc[p] # "Accepted") )

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* (they are already defined with the exact names)

====