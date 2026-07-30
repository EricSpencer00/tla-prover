---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

\* Control locations: start0 (no INIT), start1 (INIT received), sent (ECHO
\* sent to all), accept (accepted). The spec combines each receive step with
\* the protocol's immediate actions, which is what fairness covers.
Control == {"start0", "start1", "sent", "accept"}
MsgKind == {"ECHO"}
Msg == [snd : 1..N, kind : MsgKind]

VARIABLES correct, faulty, pc, inbox, sentMsgs
vars == << correct, faulty, pc, inbox, sentMsgs >>

TypeOK ==
    /\ correct \subseteq (1..N)
    /\ faulty \subseteq (1..N)
    /\ correct \cup faulty = (1..N)
    /\ correct \cap faulty = {}
    /\ pc \in [1..N -> Control]
    /\ inbox \in [1..N -> SUBSET Msg]
    /\ sentMsgs \subseteq Msg

\* A correct process may treat every Byzantine message as received, so INIT
\* does not need a privileged sender.
Init ==
    /\ \E R \in SUBSET (1..N) :
         /\ Cardinality(R) = N - F
         /\ correct = R
         /\ faulty = (1..N) \ R
    /\ \E pc0 \in {{ "start0" } \cup {"start1"}} :
         \A p \in (1..N) : pc[p] = pc0
    /\ inbox = [p \in 1..N |-> {}]
    /\ sentMsgs = {}

\* Combining reception with the protocol's immediate actions keeps the model
\* small and lets weak fairness on this single action cover both aspects.
RecAct ==
    /\ \E p \in correct :
         \E newMsgs \subseteq (sentMsgs \cup { [snd |-> q, kind |-> "ECHO"] : q \in faulty }) :
             /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \cup newMsgs]
             /\ CASE
                  /\ pc[p] = "start1"
                     /\ sentMsgs' = sentMsgs \cup { [snd |-> p, kind |-> "ECHO"] }
                     /\ pc' = [pc EXCEPT ![p] = "sent"]
                  /\ pc[p] = "start0" /\ Cardinality({ m \in inbox[p] : m.kind = "ECHO" }) >= N - 2 * T
                     /\ sentMsgs' = sentMsgs \cup { [snd |-> p, kind |-> "ECHO"] }
                     /\ pc' = [pc EXCEPT ![p] = "sent"]
                  /\ pc[p] = "start0" /\ Cardinality({ m \in inbox[p] : m.kind = "ECHO" }) >= N - T
                     /\ sentMsgs' = sentMsgs \cup { [snd |-> p, kind |-> "ECHO"] }
                     /\ pc' = [pc EXCEPT ![p] = "accept"]
                  /\ pc[p] = "sent" /\ Cardinality({ m \in inbox[p] : m.kind = "ECHO" }) >= N - T
                     /\ pc' = [pc EXCEPT ![p] = "accept"]
                  /\ \A k \in Control : k
             /\ UNCHANGED << correct, faulty >>

Quiet ==
    /\ \A p \in correct : pc[p] = "accept"
    /\ UNCHANGED vars

Spec == Init /\ [][RecAct]_vars /\ WF_vars(RecAct) /\ [][Quiet]_vars

CorrLtl == <>(\A p \in correct : pc[p] = "accept")
RelayLtl == (<> (\E p \in correct : pc[p] = "accept")) ~> (\A p \in correct : pc[p] = "accept")
UnforgLtl == (\/ \A p \in correct : pc[p] = "start0") ~> (\A p \in correct : pc[p] # "accept")

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
====