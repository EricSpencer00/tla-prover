---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

Participant == "pt"
Pids == 1 .. participants

VARIABLES vote, alive, decided, faulty, sent
Coord == "coord"

CoordSent == [p \in Pids |-> notsent]
CoordRecv == [p \in Pids |-> waiting]

\* vote/recv/CoordSent carry participant votes between the participants and
\* the coordinator; decided is each participant's final commit/abort decision.
Vars == <<vote, alive, decided, faulty, sent, CoordSent, CoordRecv,
           coordAlive, coordFaulty, coordDecided>>

TypeInv ==
  /\ vote \in [Pids -> {yes, no}]
  /\ alive \in [Pids -> BOOLEAN]
  /\ decided \in [Pids -> {undecided, commit, abort}]
  /\ faulty \in [Pids -> BOOLEAN]
  /\ sent \in [Pids -> BOOLEAN]
  /\ CoordSent \in [Pids -> {notsent} \cup [voter: {yes, no}, alive: BOOLEAN]]
  /\ CoordRecv \in [Pids -> {waiting} \cup [v: {yes, no}, a: BOOLEAN]]
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecided \in {undecided, commit, abort}

Init ==
  /\ \E v \in [Pids -> {yes, no}]:
       /\ vote = v
       /\ CoordRecv = [p \in Pids |-> waiting]
  /\ alive = [p \in Pids |-> TRUE]
  /\ decided = [p \in Pids |-> undecided]
  /\ faulty = [p \in Pids |-> FALSE]
  /\ sent = [p \in Pids |-> FALSE]
  /\ CoordSent = [p \in Pids |-> notsent]
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecided = undecided

\* Coordinator broadcast is sequential: it may leave participants undecided.
SendVoteReq(p) ==
  /\ coordAlive
  /\ CoordSent[p] = notsent
  /\ CoordSent' = [CoordSent EXCEPT ![p] = notsent]
  /\ UNCHANGED <<vote, alive, decided, faulty, sent, CoordRecv,
                 coordAlive, coordFaulty, coordDecided>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecided = undecided
  /\ CoordRecv[p] = waiting
  /\ sent[p]
  /\ CoordRecv' = [CoordRecv EXCEPT ![p] = [v |-> vote[p], a |-> alive[p]]]
  /\ UNCHANGED <<vote, alive, decided, faulty, sent, CoordSent,
                 coordAlive, coordFaulty, coordDecided>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecided = undecided
  /\ CoordRecv[p] = waiting
  /\ ~alive[p]
  /\ ~sent[p]
  /\ coordDecided' = abort
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decided, faulty, sent, CoordSent, CoordRecv,
                 coordAlive>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecided = undecided
  /\ \A p \in Pids: CoordRecv[p] # waiting
  /\ coordDecided' = IF \A p \in Pids: CoordRecv[p].v = yes
                     THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive decided, faulty, sent, CoordSent, CoordRecv,
                 coordAlive, coordFaulty>>

\* Simple broadcast: participants are reached one at a time, so a crash matters.
BroadcastCoord(p) ==
  /\ coordAlive
  /\ coordDecided # undecided
  /\ CoordSent[p] = notsent
  /\ CoordSent' = [CoordSent EXCEPT ![p] =
        [voter |-> coordDecided, alive |-> ~coordFaulty]]
  /\ UNCHANGED <<vote, alive, decided, faulty, sent, CoordRecv,
                 coordAlive, coordFaulty, coordDecided>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decided, faulty, sent, CoordSent, CoordRecv,
                 coordDecided>>

SendVote(p) ==
  /\ alive[p]
  /\ ~sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, faulty, CoordSent, CoordRecv,
                 coordAlive, coordFaulty, coordDecided>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ sent[p]
  /\ vote[p] = no
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, CoordSent, CoordRecv,
                 coordAlive, coordFaulty, coordDecided>>

AbortOnReqTimeout(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ ~coordAlive
  /\ CoordSent[p] = notsent
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, CoordSent, CoordRecv,
                 coordAlive, coordFaulty, coordDecided>>

DecideFromCoord(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ CoordSent[p] # notsent
  /\ decided' = [decided EXCEPT ![p] = IF CoordSent[p].voter = commit
                                            THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, CoordSent, CoordRecv,
                 coordAlive, coordFaulty, coordDecided>>

PartDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decided, sent, CoordSent, CoordRecv,
                 coordAlive, coordFaulty, coordDecided>>

CoordinatorProgress == SendVoteReq(1) \/ ReceiveVote(1) \/ DetectFault(1) \/ BroadcastCoord(1)
ParticipantProgress == SendVote(1) \/ AbortOnVote(1) \/ AbortOnReqTimeout(1) \/ DecideFromCoord(1)

Next ==
  \/ \E p \in Pids: SendVoteReq(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ BroadcastCoord(p) \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnReqTimeout(p) \/ DecideFromCoord(p) \/ PartDie(p)
  \/ MakeDecision \/ CoordDie

Spec ==
  /\ Init /\ [][Next]_Vars
  /\ WF_Vars(CoordinatorProgress)
  /\ WF_Vars(ParticipantProgress)

\* No two participants may decide differently: commit vs abort is exclusive.
AC1 == \A p, q \in Pids: (decided[p] = commit /\ decided[q] = abort) => FALSE
AC2 == (\E p \in Pids: decided[p] = commit) => (\A q \in Pids: vote[q] = yes)
AC3 == (\E p \in Pids: decided[p] = abort) => (\E q \in Pids: vote[q] = no \/ faulty[q] \/ coordFaulty)
AC4 == (\A p \in Pids: decided[p] = commit) ~> (\A p \in Pids: decided[p] = commit)
AC5 == (\A p \in Pids: decided[p] = undecided) ~> (\E p \in Pids: decided[p] # undecided)

\* Simple broadcast can drop a decision on a crashed coordinator, so AC5 is
\* not included in the properties checked for this variant.
Properties == AC1 /\ AC2 /\ AC3 /\ AC4

====