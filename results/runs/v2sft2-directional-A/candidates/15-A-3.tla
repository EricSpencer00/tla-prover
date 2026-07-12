---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

VARIABLES Correct, Faulty, Loc, Recv, Sent, Accept

(* ----------------------------------------------------------------- *)
(* Constants that the configuration will instantiate *)
CONSTANTS N, T, F

(* ----------------------------------------------------------------- *)
(* Derived parameter: maximal number of faulty processes in the model *)
ASSUME N > 3*T
ASSUME T >= F
ASSUME 0 <= F

(* ----------------------------------------------------------------- *)
(* Types *)
\* Process identifiers
Process == 1..N

\* Message type: only ECHO is used
MsgType == {"ECHO"}

\* A message is a pair <sender, type>
Message == [sender \in Process, mtype \in MsgType]

\* Control locations for correct processes
LocType == {"StartNonBcast", "StartBcast", "WaitEchos", "SentEchos", "Accepted"}

\* Types for state variables
CorrectSet == [p \in Process |-> Boolean]
LocSet == [p \in Process |-> LocType]
RecvSet == [p \in Process |-> SUBSET Message]
SentSet == [p \in Process |-> SUBSET Message]
AcceptSet == [p \in Process |-> Boolean]

(* ----------------------------------------------------------------- *)
(* Helper predicates *)

\* True when a process is correct
IsCorrect(p) == Correct[p]

\* True when a process is faulty
IsFaulty(p) == Faulty[p]

\* Correct processes must belong to the complement of faulty set
CorrectFaultyDisjoint == \A p \in Process: (Correct[p] <=> ~Faulty[p])

\* Count of messages of a given type received by a process
CountEchos(p) == Cardinality({m \in Recv[p] : m.mtype = "ECHO"})

(* ----------------------------------------------------------------- *)
(* Initial state *)

Init ==
    /\ Correct = [p \in Process |-> TRUE] \* will be overridden
    /\ Faulty = [p \in Process |-> FALSE] \* will be overridden
    /\ UNCHANGED<<Loc, Recv, Sent, Accept>>
    /\ Correct = {p \in Process : ~ Faulty[p]}
    /\ Faulty = {p \in Process : Faulty[p]}
    /\ \A p \in Process: 
          (IsCorrect(p) => 
               (Loc[p] \in {"StartNonBcast", "StartBcast"} /\ 
                Recv[p] = {} /\ 
                Sent[p] = {} /\ 
                Accept[p] = FALSE))
    /\ \A p \in Process: ~IsCorrect(p) => 
               (Loc[p] = "StartNonBcast" /\ 
                Recv[p] = {} /\ 
                Sent[p] = {} /\ 
                Accept[p] = FALSE)

\* Restricted initial state where no correct process received the INIT message
InitNoBcast ==
    /\ Init
    /\ \A p \in Process: IsCorrect(p) => Loc[p] = "StartNonBcast"

\* The actual INIT predicate used by the spec (allows either Init or InitNoBcast)
INIT == Init \/ InitNoBcast

(* ----------------------------------------------------------------- *)
(* Actions *)

\* Correct process receives a set of new messages
RecvMsg(p, NewMsgs) ==
    /\ IsCorrect(p)
    /\ NewMsgs \subseteq (Sent \cup MessagesFromFaulty)
    /\ Recv' = [Recv EXCEPT ![p] = @ \cup NewMsgs]
    /\ UNCHANGED <<Correct, Faulty, Loc, Sent, Accept>>

\* Helper: all possible messages that Byzantine processes could have sent
MessagesFromFaulty ==
    { [sender |-> s, mtype |-> "ECHO"] : s \in Faulty }

\* Correct process that has the INIT message sends an ECHO
SendEcho(p) ==
    /\ IsCorrect(p)
    /\ Loc[p] = "StartBcast"
    /\ Loc' = [Loc EXCEPT ![p] = "WaitEchos"]
    /\ Sent' = [Sent EXCEPT ![p] = @ \cup { [sender |-> p, mtype |-> "ECHO"] }]
    /\ UNCHANGED <<Correct, Faulty, Recv, Accept>>

\* Correct process that has not yet sent ECHO, receives enough ECHOs to send one
SendEchoByThreshold(p) ==
    /\ IsCorrect(p)
    /\ Loc[p] \in {"StartNonBcast", "WaitEchos"}
    /\ CountEchos(p) >= N - 2*T
    /\ CountEchos(p) < N - T
    /\ Loc' = [Loc EXCEPT ![p] = "SentEchos"]
    /\ Sent' = [Sent EXCEPT ![p] = @ \cup { [sender |-> p, mtype |-> "ECHO"] }]
    /\ UNCHANGED <<Correct, Faulty, Recv, Accept>>

\* Correct process that has not yet sent ECHO, receives enough ECHOs to accept
AcceptByThreshold(p) ==
    /\ IsCorrect(p)
    /\ Loc[p] \in {"StartNonBcast", "WaitEchos"}
    /\ CountEchos(p) >= N - T
    /\ Loc' = [Loc EXCEPT ![p] = "Accepted"]
    /\ Accept' = [Accept EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<Correct, Faulty, Recv, Sent>>

\* Correct process that has sent ECHO, later receives enough ECHOs to accept
AcceptAfterSent(p) ==
    /\ IsCorrect(p)
    /\ Loc[p] = "SentEchos"
    /\ CountEchos(p) >= N - T
    /\ Loc' = [Loc EXCEPT ![p] = "Accepted"]
    /\ Accept' = [Accept EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<Correct, Faulty, Recv, Sent>>

\* The combined next-state relation for any single process step
Next ==
    \/ \E p \in Correct : RecvMsg(p, NewMsgs)
    \/ \E p \in Correct : SendEcho(p)
    \/ \E p \in Correct : SendEchoByThreshold(p)
    \/ \E p \in Correct : AcceptByThreshold(p)
    \/ \E p \in Correct : AcceptAfterSent(p)

(* ----------------------------------------------------------------- *)
(* Specification *)

Spec == Init /\ [][Next]_<<Correct, Faulty, Loc, Recv, Sent, Accept>>

(* ----------------------------------------------------------------- *)
(* Type safety invariant *)

TypeOK ==
    /\ Correct \subseteq [p \in Process |-> TRUE]
    /\ Faulty \subseteq [p \in Process |-> FALSE]
    /\ CorrectFaultyDisjoint
    /\ \A p \in Process: IsCorrect(p) => Loc[p] \in LocType
    /\ \A p \in Process: Recv[p] \subseteq [sender \in Process, mtype \in MsgType]
    /\ \A p \in Process: Sent[p] \subseteq [sender \in Process, mtype \in MsgType]
    /\ \A p \in Process: Accept[p] \in BOOLEAN

(* ----------------------------------------------------------------- *)
(* Fast-consistency constraints (used by the paper, kept for completeness) *)

FCConstraints ==
    \A p \in Correct : 
        (Loc[p] = "SentEchos" \/ Loc[p] = "Accepted") => 
            CountEchos(p) >= N - 2*T

(* ----------------------------------------------------------------- *)
(* Liveness properties *)

CorrLtl == [](<> /\ \A p \in Correct : Accept[p])

RelayLtl == [](<> /\ \E p \in Correct : Accept[p]) => [](<> /\ \A q \in Correct : Accept[q])

UnforgLtl == [](~(\E p \in Correct : Accept[p]))

====