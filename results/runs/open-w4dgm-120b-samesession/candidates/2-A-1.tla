---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

Recipient == {p \in participants : p # "coord"}

VARIABLES vote, alive, decision, faulty, sent, cstate, fwd

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ cstate \in {"waiting", "voting", "broadcasted", "decided"}
  /\ fwd \in [participants -> [participants \cup {"coord"} -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ cstate = "waiting"
  /\ fwd = [p \in participants |-> [q \in participants \cup {"coord"} |-> notsent]]

SendReq ==
  /\ alive["coord"]
  /\ cstate = "waiting"
  /\ cstate' = "voting"
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, fwd>>

\* The coordinator collects every still-responding participant's vote.
GetVote(p) ==
  /\ alive["coord"]
  /\ cstate = "voting"
  /\ alive[p]
  /\ ~sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ UNCHANGED <<alive, decision, faulty, cstate, fwd>>

DetectFault(p) ==
  /\ alive["coord"]
  /\ cstate = "voting"
  /\ ~alive[p]
  /\ ~sent[p]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, sent, cstate, fwd>>

Decide(v) ==
  /\ alive["coord"]
  /\ cstate = "voting"
  /\ \A p \in participants : (alive[p] => vote[p] = v)
  /\ decision' = [p \in participants |-> IF v = yes THEN commit ELSE abort]
  /\ fwd' = [p \in participants |->
        [q \in participants \cup {"coord"} |->
           IF q = "coord" THEN v ELSE notsent]]
  /\ cstate' = "broadcasted"
  /\ UNCHANGED <<vote, alive, sent, faulty>>

Broadcast ==
  /\ alive["coord"]
  /\ cstate = "broadcasted"
  /\ \E p \in participants : alive[p] /\ fwd[p]["coord"] = notsent
  /\ fwd' = [p \in participants |->
        [fwd[p] EXCEPT !["coord"] = decision[p]]]
  /\ UNCHANGED <<vote, alive, decision, sent, faulty, cstate>>

Die == /\ alive["coord"]
        /\ alive' = [alive EXCEPT !["coord"] = FALSE]
        /\ UNCHANGED <<vote, decision, sent, faulty, cstate, fwd>>

\* A participant that has not yet received any pre-decision inherits one
\* from the coordinator's own broadcast to it.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p]["coord"] # notsent
  /\ fwd' = [fwd EXCEPT ![p]["coord"] = fwd[p]["coord"]]
  /\ UNCHANGED <<vote, alive, decision, sent, faulty, cstate>>

\* A participant may also inherit a pre-decision from another participant
\* that forwarded it, which is what makes delivery non-blocking on the
\* coordinator.
PreDecideFromPeer(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p]["coord"] = notsent
  /\ \E q \in participants :
        /\ q # p
        /\ fwd[q][p] # notsent
        /\ fwd' = [fwd EXCEPT ![p][q] = fwd[q][p]]
  /\ UNCHANGED <<vote, alive, decision, sent, faulty, cstate>>

\* Forwarding continues until a participant has sent its pre-decision to
\* every other participant.
Forward(p, q) ==
  /\ alive[p]
  /\ p # q
  /\ fwd[p][q] = notsent
  /\ fwd[p]["coord"] # notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p]["coord"]]
  /\ UNCHANGED <<vote, alive, decision, sent, faulty, cstate>>

DecideNB(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ fwd[p]["coord"] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p]["coord"]]
  /\ UNCHANGED <<vote, alive, sent, faulty, cstate, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~alive["coord"]
  /\ (\A q \in participants : fwd[q]["coord"] = notsent)
  /\ (\A q \in participants : (alive[q] => fwd[q][p] = notsent))
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, sent, faulty, cstate, fwd>>

\* A permanent crash (the blocking case) is still a possible failure of a
\* participant that has not yet decided, and it does not set a decision.
Die(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<vote, decision, sent, faulty, cstate, fwd>>

Next ==
  \/ SendReq \/ Broadcast \/ Die
  \/ \E v \in {yes, no} : Decide(v)
  \/ \E p \in participants :
        \/ GetVote(p) \/ DetectFault(p) \/ PreDecideFromCoord(p) \/ PreDecideFromPeer(p)
        \/ DecideNB(p) \/ AbortOnTimeout(p) \/ Die(p)
        \/ \E q \in participants : Forward(p, q)

SpecNB ==
  /\ Init /\ [][Next]_<<vote, alive, decision, sent, faulty, cstate, fwd>>
  /\ WF_Vars(PreDecideFromCoord("p1") \/ PreDecideFromPeer("p1") \/ DecideNB("p1"))
  /\ WF_Vars(PreDecideFromCoord("p2") \/ PreDecideFromPeer("p2") \/ DecideNB("p2"))
  /\ WF_Vars(PreDecideFromCoord("p3") \/ PreDecideFromPeer("p3") \/ DecideNB("p3"))
  /\ WF_Vars(DecideNB("p4"))

\* No two participants ever reach different decisions.
AC1 ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

\* Committing requires unanimity.
AC2 ==
  (\E p \in participants : decision[p] = commit) => \A p \in participants : vote[p] = yes

\* Aborting needs a no vote or a failure.
AC3 ==
  (\E p \in participants : decision[p] = abort) =>
    (\E p \in participants : vote[p] = no) \/ (\E p \in participants : faulty[p]) \/ ~alive["coord"]

\* A decided participant never reverts.
AC4 ==
  \A p \in participants :
    decision[p] # undecided => (decision[p] = commit \/ decision[p] = abort)

\* Every non-faulty participant eventually decides: this is the non-blocking
\* guarantee that the reliable broadcast delivers even if the coordinator
\* crashes mid-broadcast.
AC5 ==
  \A p \in participants : (decision[p] = undecided /\ alive[p]) ~> (decision[p] # undecided)

====