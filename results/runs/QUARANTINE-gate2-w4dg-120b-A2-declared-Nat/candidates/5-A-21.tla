---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentvote, sentreq, recv, sentdec

vars == <<vote, alive, decision, faulty, sentvote, sentreq, recv, sentdec>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants \cup {"coord"} -> {undecided, commit, abort}]
  /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
  /\ sentvote \in [participants -> BOOLEAN]
  /\ sentreq \in [participants -> BOOLEAN]
  /\ recv \in [participants -> {yes, no, waiting}]
  /\ sentdec \in [participants -> {commit, abort, notsent}]

Init ==
  /\ \E initvote \in [participants -> {yes, no}]:
       vote = initvote
  /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
  /\ decision = [p \in participants \cup {"coord"} |-> undecided]
  /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
  /\ sentvote = [p \in participants |-> FALSE]
  /\ sentreq = [p \in participants |-> FALSE]
  /\ recv = [p \in participants |-> waiting]
  /\ sentdec = [p \in participants |-> notsent]

SendReq ==
  /\ alive["coord"]
  /\ \E p \in participants:
       /\ ~sentreq[p]
       /\ sentreq' = [sentreq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, recv, sentdec>>

ReceiveVote ==
  /\ alive["coord"]
  /\ decision["coord"] = undecided
  /\ \A p \in participants: sentreq[p]
  /\ \E p \in participants:
       /\ recv[p] = waiting
       /\ sentvote[p]
       /\ recv' = [recv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, sentreq, sentdec>>

DetectFault ==
  /\ alive["coord"]
  /\ decision["coord"] = undecided
  /\ \A p \in participants: sentreq[p]
  /\ \E p \in participants:
       /\ recv[p] = waiting
       /\ ~alive[p]
       /\ decision' = [decision EXCEPT !["coord"] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentvote, sentreq, recv, sentdec>>

MakeDecision ==
  /\ alive["coord"]
  /\ decision["coord"] = undecided
  /\ \A p \in participants: recv[p] # waiting
  /\ decision' = [decision EXCEPT !["coord"] =
                    IF \A p \in participants: recv[p] = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, faulty, sentvote, sentreq, recv, sentdec>>

Broadcast ==
  /\ alive["coord"]
  /\ decision["coord"] \in {commit, abort}
  /\ \E p \in participants:
       /\ sentdec[p] = notsent
       /\ sentdec' = [sentdec EXCEPT ![p] = decision["coord"]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, sentreq, recv>>

CoordDie ==
  /\ alive["coord"]
  /\ alive' = [alive EXCEPT !["coord"] = FALSE]
  /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
  /\ UNCHANGED <<vote, decision, sentvote, sentreq, recv, sentdec>>

SendVote ==
  /\ \E p \in participants:
       /\ alive[p]
       /\ sentreq[p]
       /\ ~sentvote[p]
       /\ sentvote' = [sentvote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentreq, recv, sentdec>>

AbortOnVote ==
  /\ \E p \in participants:
       /\ alive[p]
       /\ sentvote[p]
       /\ decision[p] = undecided
       /\ vote[p] = no
       /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentvote, sentreq, recv, sentdec>>

AbortOnTimeout ==
  /\ \E p \in participants:
       /\ alive[p]
       /\ decision[p] = undecided
       /\ ~alive["coord"]
       /\ ~sentreq[p]
       /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentvote, sentreq, recv, sentdec>>

DecideFromBroadcast ==
  /\ \E p \in participants:
       /\ alive[p]
       /\ decision[p] = undecided
       /\ sentdec[p] # notsent
       /\ decision' = [decision EXCEPT ![p] = sentdec[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentvote, sentreq, recv, sentdec>>

ParticipantDie ==
  /\ \E p \in participants:
       /\ alive[p]
       /\ alive' = [alive EXCEPT ![p] = FALSE]
       /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentvote, sentreq, recv, sentdec>>

Next ==
  \/ SendReq \/ ReceiveVote \/ DetectFault \/ MakeDecision \/ Broadcast \/ CoordDie
  \/ SendVote \/ AbortOnVote \/ AbortOnTimeout \/ DecideFromBroadcast \/ ParticipantDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendReq)
  /\ WF_vars(ReceiveVote)
  /\ WF_vars(SendVote)
  /\ WF_vars(AbortOnVote)
  /\ WF_vars(DecideFromBroadcast)

Agreement ==
  \A p, q \in participants:
    ~(decision[p] = commit /\ decision[q] = abort)

CommitValidity ==
  \A p \in participants: decision[p] = commit => (\A q \in participants: vote[q] = yes)

AbortValidity ==
  \A p \in participants: decision[p] = abort =>
    \/ \E q \in participants: vote[q] = no
    \/ \E q \in participants: faulty[q]
    \/ faulty["coord"]

Irrevocability ==
  \A p \in participants:
    /\ (decision[p] = commit => (\A fv \in {commit, abort}: decision[p] = fv))
    /\ (decision[p] = abort => (\A fv \in {commit, abort}: decision[p] = fv))

TerminateEventually ==
  <>(\A p \in participants: decision[p] # undecided \/ faulty[p] \/ faulty["coord"])

====