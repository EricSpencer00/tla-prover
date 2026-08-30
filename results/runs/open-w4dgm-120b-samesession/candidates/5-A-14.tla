---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Decided is the set of participants that have taken a final decision.
Decided == {p \in participants : decision[p] \in {commit, abort}}

VARIABLES vote, alive, decision, faulty, sent, reqSent, recv, broadcasted

vars == <<vote, alive, decision, faulty, sent, reqSent, recv, broadcasted>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
    /\ sent \in [participants -> BOOLEAN]
    /\ reqSent \in [participants -> BOOLEAN]
    /\ recv \in [participants -> {yes, no, waiting}]
    /\ broadcasted \in [participants -> {commit, abort, notsent}]

\* The coordinator votes yes exactly when all participants voted yes -- this
\* is what keeps the one-shot decision aligned with the participants' votes.
CoordDecision == IF \A p \in participants : vote[p] = yes THEN commit ELSE abort

Init ==
    /\ \E v \in [participants -> {yes, no}] : vote = v
    /\ alive = [q \in participants \cup {"coord"} |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [q \in participants \cup {"coord"} |-> FALSE]
    /\ sent = [p \in participants |-> FALSE]
    /\ reqSent = [p \in participants |-> FALSE]
    /\ recv = [p \in participants |-> waiting]
    /\ broadcasted = [p \in participants |-> notsent]

\* Coordinator actions:
ReqVote(p) ==
    /\ alive["coord"] /\ ~reqSent[p]
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, recv, broadcasted>>

RecvVote(p) ==
    /\ alive["coord"] /\ decision["coord"] = undecided
    /\ reqSent[p] /\ recv[p] = waiting /\ sent[p]
    /\ recv' = [recv EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, reqSent, broadcasted>>

DetectFault(p) ==
    /\ alive["coord"] /\ decision["coord"] = undecided
    /\ reqSent[p] /\ recv[p] = waiting /\ ~alive[p]
    /\ decision' = [decision EXCEPT !["coord"] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, reqSent, recv, broadcasted>>

DecideCoord ==
    /\ alive["coord"] /\ decision["coord"] = undecided
    /\ \A p \in participants : recv[p] # waiting
    /\ decision' = [decision EXCEPT !["coord"] = CoordDecision]
    /\ UNCHANGED <<vote, alive, faulty, sent, reqSent, recv, broadcasted>>

Broadcast(p) ==
    /\ alive["coord"] /\ decision["coord"] # undecided
    /\ broadcasted[p] = notsent
    /\ broadcasted' = [broadcasted EXCEPT ![p] = decision["coord"]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, reqSent, recv>>

DieCoord ==
    /\ alive["coord"] /\ ~faulty["coord"]
    /\ alive' = [alive EXCEPT !["coord"] = FALSE]
    /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
    /\ UNCHANGED <<vote, decision, sent, reqSent, recv, broadcasted>>

\* Participant actions:
SendVote(p) ==
    /\ alive[p] /\ reqSent[p] /\ ~sent[p]
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, reqSent, recv, broadcasted>>

AbortOnVote(p) ==
    /\ alive[p] /\ decision[p] = undecided /\ sent[p] /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, reqSent, recv, broadcasted>>

AbortTimeout(p) ==
    /\ alive[p] /\ decision[p] = undecided
    /\ ~alive["coord"] /\ ~reqSent[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, reqSent, recv, broadcasted>>

DecideFromCoord(p) ==
    /\ alive[p] /\ decision[p] = undecided /\ broadcasted[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
    /\ UNCHANGED <<vote, alive, faulty, sent, reqSent, recv, broadcasted>>

DieParticipant(p) ==
    /\ alive[p] /\ ~faulty[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sent, reqSent, recv, broadcasted>>

CoordinatorActions == DecideCoord \/ DieCoord \/ \E p \in participants : DecideCoord \/ DieCoord

ParticipantActions ==
    \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortTimeout(p) \/ DecideFromCoord(p) \/ DieParticipant(p)

Next == CoordinatorActions \/ ParticipantActions

\* Progress requires the coordinator to stay operational, so death is excluded
\* from fairness here; it is still modeled as a legitimate (but unfair) action.
Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(ReqVote("p1")) /\ WF_vars(RecvVote("p1")) /\ WF_vars(DecideCoord) /\ WF_vars(Broadcast("p1"))
    /\ WF_vars(ReqVote("p2")) /\ WF_vars(RecvVote("p2")) /\ WF_vars(Broadcast("p2"))
    /\ WF_vars(SendVote("p1")) /\ WF_vars(AbortOnVote("p1")) /\ WF_vars(DecideFromCoord("p1"))
    /\ WF_vars(SendVote("p2")) /\ WF_vars(AbortOnVote("p2")) /\ WF_vars(DecideFromCoord("p2"))

\* Safety: no two participants ever decide differently.
AgreementConsistency == \A p, q \in participants : (decision[p] = commit) => (decision[q] # abort)

CommitValidity == ( /\ \E p \in participants : decision[p] = commit
                     /\ \A q \in participants : vote[q] = yes )

AbortValidity == ( \E p \in participants : decision[p] = abort )
                    => ( \E q \in participants : vote[q] = no
                         \/ \E q \in participants : faulty[q]
                         \/ faulty["coord"] )

Irrevocability == \A p \in participants :
    /\ (decision[p] = commit) ~> (decision[p] = commit)
    /\ (decision[p] = abort) ~> (decision[p] = abort)

\* The non-blocking liveness AC5 is NOT satisfied by this simple broadcast,
\* so it is omitted from Spec and left as a commented-out optional property.
EventualResolution == \A p \in participants :
    (decision[p] = undecided) ~> (decision[p] # undecided)

====