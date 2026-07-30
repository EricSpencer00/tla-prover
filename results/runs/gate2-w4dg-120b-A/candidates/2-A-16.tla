---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME yes # no

VARIABLES participant, alive, decision, faulty, voteSent, coordReq, coordVote,
         coordBroad, coordDecision, coordAlive, coordFaulty, forwarding

vars == <<participant, alive, decision, faulty, voteSent, coordReq, coordVote,
         coordBroad, coordDecision, coordAlive, coordFaulty, forwarding>>

None == "none"

TypeOK ==
  /\ participant \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ voteSent \subseteq participants
  /\ coordReq \in {None, waiting}
  /\ coordVote \in {None, yes, no}
  /\ coordBroad \subseteq participants
  /\ coordDecision \in {None, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \subseteq participants
  /\ forwarding \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ participant = [p \in participants |-> yes]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ voteSent = {}
  /\ coordReq = None
  /\ coordVote = None
  /\ coordBroad = {}
  /\ coordDecision = None
  /\ coordAlive = TRUE
  /\ coordFaulty = {}
  /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

SendREQ ==
  /\ coordAlive
  /\ coordReq = None
  /\ coordReq' = waiting
  /\ UNCHANGED <<participant, alive, decision, faulty, voteSent, coordVote,
                coordBroad, coordDecision, coordAlive, coordFaulty, forwarding>>

GetVote(p) ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ p \notin voteSent
  /\ coordVote' = IF coordVote = None THEN participant[p] ELSE coordVote
  /\ voteSent' = voteSent \cup {p}
  /\ UNCHANGED <<participant, alive, decision, faulty, coordReq, coordBroad,
                coordDecision, coordAlive, coordFaulty, forwarding>>

DetectCoordFault ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ coordAlive' = FALSE
  /\ coordFaulty' = coordFaulty \cup participants
  /\ UNCHANGED <<participant, alive, decision, faulty, voteSent, coordVote,
                coordBroad, coordDecision, forwarding>>

MakeDecision ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ coordVote # None
  /\ coordDecision' = coordVote
  /\ UNCHANGED <<participant, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroad, coordAlive, coordFaulty, forwarding>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # None
  /\ p \notin coordBroad
  /\ coordBroad' = coordBroad \cup {p}
  /\ UNCHANGED <<participant, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordDecision, coordAlive, coordFaulty, forwarding>>

Die ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = coordFaulty \cup participants
  /\ UNCHANGED <<participant, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroad, coordDecision, forwarding>>

SendVote(p) ==
  /\ alive[p]
  /\ p \notin voteSent
  /\ voteSent' = voteSent \cup {p}
  /\ UNCHANGED <<participant, alive, decision, faulty, coordReq, coordVote,
                coordBroad, coordDecision, coordAlive, coordFaulty, forwarding>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ participant[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<participant, alive, faulty, voteSent, coordReq, coordVote,
                coordBroad, coordDecision, coordAlive, coordFaulty, forwarding>>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ coordBroad \cap participants = {}
  /\ \A q \in participants : partitionedAlive(q) # {}
  /\ \A q \in participants : q \notin faulty => \A r \in participants : forwarding[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<participant, alive, faulty, voteSent, coordReq, coordVote,
                coordBroad, coordDecision, coordAlive, coordFaulty, forwarding>>

PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forwarding[p][p] = notsent
  /\ p \in coordBroad
  /\ coordDecision # None
  /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED <<participant, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroad, coordDecision, coordAlive, coordFaulty>>

PreDecideFromForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forwarding[p][p] = notsent
  /\ \E q \in participants :
        /\ q # p
        /\ forwarding[q][p] # notsent
        /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
  /\ UNCHANGED <<participant, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroad, coordDecision, coordAlive, coordFaulty>>

Forward(p, q) ==
  /\ alive[p]
  /\ alive[q]
  /\ p # q
  /\ forwarding[p][p] # notsent
  /\ forwarding[p][q] = notsent
  /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
  /\ UNCHANGED <<participant, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroad, coordDecision, coordAlive, coordFaulty>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forwarding[p][p] # notsent
  /\ \A q \in participants : q # p => forwarding[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = forwarding[p][p]]
  /\ UNCHANGED <<participant, alive, faulty, voteSent, coordReq, coordVote,
                coordBroad, coordDecision, coordAlive, coordFaulty, forwarding>>

DieP(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<participant, decision, voteSent, coordReq, coordVote,
                coordBroad, coordDecision, coordAlive, coordFaulty, forwarding>>

ProgressP == \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortTimeout(p)
             \/ PreDecideFromCoord(p) \/ PreDecideFromForward(p) \/ Decide(p)
             \/ DieP(p)

ProgressCoord == SendREQ \/ DetectCoordFault \/ MakeDecision \/ Die

Next == ProgressP \/ ProgressCoord
        \/ \E p \in participants : Broadcast(p)
        \/ \E p \in participants, q \in participants : Forward(p, q)

SpecNB == Init /\ [][Next]_vars
           /\ WF_vars(ProgressP) /\ WF_vars(ProgressCoord)

TypeInvNB == TypeOK

AC1 == ~ (\E p \in participants : decision[p] = commit /\ \E q \in participants : decision[q] = abort)
AC2 == (\E p \in participants : decision[p] = commit) => (\A q \in participants : participant[q] = yes)
AC3 == (\E p \in participants : decision[p] = abort) => (typeOK \/ (coordFaulty # {}))
AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)
AC5 == \A p \in participants : (p \notin faulty) ~> (decision[p] = commit \/ decision[p] = abort)

partitionedAlive(p) == {q \in participants : alive[q] /\ p \in coordBroad}
PROPERTIES == AC3 /\ AC5

====