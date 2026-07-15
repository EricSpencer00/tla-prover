---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT N, T, F

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1 .. N
ECHO == "ECHO"

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    correct,        \* Set of correct processes
    faulty,         \* Set of faulty processes (complement of correct)
    pc,             \* Control location of each process
    received,       \* Set of messages each process has received
    sent             \* Set of ECHO messages sent by correct processes

\* ----------------------------------------------------------------------
\* Types for readability
\* ----------------------------------------------------------------------
PCVals == {"InitNo", "InitYes", "SentEcho", "Accepted"}

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ correct \subseteq Proc
    /\ Cardinality(correct) = N - F
    /\ faulty = Proc \ correct
    /\ pc \in [Proc -> PCVals]
       \* Assign each process either InitNo or InitYes nondeterministically
    /\ \A i \in Proc : pc[i] \in {"InitNo", "InitYes"}
    /\ received = [i \in Proc |-> {}]
    /\ sent = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Helper: set of all possible ECHO messages (sender, type)
AllMsgs == { <<s, ECHO>> : s \in Proc }

\* Receive a subset of messages (including arbitrary Byzantine messages)
Receive(i) ==
    /\ i \in correct
    /\ \E new \subseteq AllMsgs :
          /\ received' = [received EXCEPT ![i] = received[i] \cup new]
          /\ UNCHANGED <<correct, faulty, pc, sent>>

\* If the process started with InitYes, it immediately sends its own ECHO
SendEchoFromInit(i) ==
    /\ i \in correct
    /\ pc[i] = "InitYes"
    /\ pc' = [pc EXCEPT ![i] = "Accepted"]
    /\ sent' = sent \cup {<<i, ECHO>>}
    /\ received' = [received EXCEPT ![i] = received[i] \cup {<<i, ECHO>>}]
    /\ UNCHANGED <<correct, faulty>>

\* Process that has not yet sent ECHO but receives enough ECHOs to send (but not accept)
SendEchoWithoutAccept(i) ==
    /\ i \in correct
    /\ pc[i] \in {"InitNo", "SentEcho"}
    /\ LET echofrom == { s \in Proc : <<s, ECHO>> \in received[i] } IN
       /\ Cardinality(echofrom) >= N - 2*T
       /\ Cardinality(echofrom) < N - T
    /\ pc' = [pc EXCEPT ![i] = "SentEcho"]
    /\ sent' = sent \cup {<<i, ECHO>>}
    /\ received' = [received EXCEPT ![i] = received[i] \cup {<<i, ECHO>>}]
    /\ UNCHANGED <<correct, faulty>>

\* Process that receives enough ECHOs to both send and accept (if not yet sent)
SendEchoAndAccept(i) ==
    /\ i \in correct
    /\ pc[i] \in {"InitNo", "SentEcho"}
    /\ LET echofrom == { s \in Proc : <<s, ECHO>> \in received[i] } IN
       /\ Cardinality(echofrom) >= N - T
    /\ pc' = [pc EXCEPT ![i] = "Accepted"]
    /\ sent' = sent \cup {<<i, ECHO>>}
    /\ received' = [received EXCEPT ![i] = received[i] \cup {<<i, ECHO>>}]
    /\ UNCHANGED <<correct, faulty>>

\* Process that has already sent ECHO and now receives enough ECHOs to accept
AcceptAfterEcho(i) ==
    /\ i \in correct
    /\ pc[i] = "SentEcho"
    /\ LET echofrom == { s \in Proc : <<s, ECHO>> \in received[i] } IN
       /\ Cardinality(echofrom) >= N - T
    /\ pc' = [pc EXCEPT ![i] = "Accepted"]
    /\ UNCHANGED <<received, sent, correct, faulty>>

\* No-op for faulty processes (they may act arbitrarily; we abstract them)
FaultyStutter ==
    /\ UNCHANGED <<correct, faulty, pc, received, sent>>

Next ==
    \/ \E i \in Proc : Receive(i)
    \/ \E i \in correct : SendEchoFromInit(i)
    \/ \E i \in correct : SendEchoWithoutAccept(i)
    \/ \E i \in correct : SendEchoAndAccept(i)
    \/ \E i \in correct : AcceptAfterEcho(i)
    \/ FaultyStutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<correct, faulty, pc, received, sent>>

\* ----------------------------------------------------------------------
\* TypeOK invariant (Type safety)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ pc \in [Proc -> PCVals]
    /\ received \in [Proc -> SUBSET AllMsgs]
    /\ sent \subseteq AllMsgs

\* ----------------------------------------------------------------------
\* FCConstraints invariant (the safety property described)
\*   No correct process accepts if no correct process started with InitYes.
\* ----------------------------------------------------------------------
FCConstraints ==
    ( \A i \in correct : pc[i] # "Accepted" )
        => ( \A i \in correct : pc[i] # "Accepted" )

\* The above is trivially true; the real intended invariant is:
Unforgeability ==
    ( \A i \in correct : pc[i] # "InitYes" )
        => ( \A i \in correct : pc[i] # "Accepted" )

\* ----------------------------------------------------------------------
\* Liveness properties (expressed in TLA+ temporal logic)
\* ----------------------------------------------------------------------
CorrLtl == 
    ( \A i \in correct : pc[i] = "InitYes" ) => <> ( \A i \in correct : pc[i] = "Accepted" )

RelayLtl ==
    ( \E i \in correct : pc[i] = "Accepted" ) => <> ( \A i \in correct : pc[i] = "Accepted" )

UnforgLtl == <> ( \A i \in correct : pc[i] = "Accepted" ) => FALSE

\* ----------------------------------------------------------------------
\* THEOREMS (optional, for model checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Unforgeability
THEOREM Spec => CorrLtl
THEOREM Spec => RelayLtl

====