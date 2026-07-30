---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Base (simple broadcast) state, reused from the reference protocol:
VARIABLES vote, alive, decision, faulty, voteSent, coordReq, coordVote,
         coordBroadcast, coordDecision, coordAlive, coordFaulty

VARIABLES
  \* Reliable broadcast forwarding table: each participant's record of what
  \* it received from the coordinator and what it forwarded to others.
  fwd

vars == <<vote, alive, decision, faulty, voteSent, coordReq,
          coordVote, coordBroadcast, coordDecision,
          coordAlive, coordFaulty, fwd>>

CoordPart == CHOOSE p \in participants : TRUE
Others(p)  == participants \ {p}

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordReq = waiting
  /\ coordVote = undecided
  /\ coordBroadcast = [p \in participants |-> undecided]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions: exactly as in the base simple broadcast protocol.
SendRequest(p) ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ p = CoordPart
  /\ coordReq' = p
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

GetVote(p) ==
  /\ p = coordReq
  /\ coordAlive
  /\ alive[p]
  /\ \A q \in participants : alive[q]
  /\ voteSent[p] = FALSE
  /\ vote[p] = undecided
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

DetectFault ==
  /\ coordAlive
  /\ coordReq # waiting
  /\ coordVote = undecided
  /\ coordFaulty' = TRUE
  /\ coordAlive' = FALSE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroadcast, coordDecision, fwd>>

MakeDecision(p) ==
  /\ p = coordReq
  /\ voteSent[p]
  /\ coordAlive
  /\ \A q \in participants : alive[q]
  /\ vote[p] # undecided
  /\ coordVote = undecided
  /\ coordVote' = vote[p]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Broadcast(p) ==
  /\ p = coordReq
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordVote # undecided
  /\ coordDecision' = coordVote
  /\ coordBroadcast' = [q \in participants |-> coordVote]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordAlive, coordFaulty, fwd>>

Die(p) ==
  /\ p = coordReq
  /\ coordAlive
  /\ coordFaulty' = TRUE
  /\ coordAlive' = FALSE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroadcast, coordDecision, fwd>>

\* Participant actions: the two pre-decision actions (from coordinator,
\* from forwarding) are what make the reliable broadcast coherent.  A
\* participant finalizes only after receiving-and-forwarding to everyone.
SendVote(p) ==
  /\ alive[p]
  /\ vote[p] = undecided
  /\ vote[p] # coordVote
  /\ vote[p] # decision[p]
  /\ voteSent[p] = FALSE
  /\ vote' = [vote EXCEPT ![p] = yes]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ vote[p] = no
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ coordBroadcast[p] # undecided
  /\ fwd' = [fwd EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroadcast, coordDecision, coordAlive,
                coordFaulty>>

PreDecideFromForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ \E q \in participants : q # p /\ alive[q] /\ fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = \E q \in participants :
                IF q # p /\ alive[q] /\ fwd[q][p] # notsent THEN fwd[q][p] ELSE notsent]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroadcast, coordDecision, coordAlive,
                coordFaulty>>

Forward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] # notsent
  /\ \E q \in Others(p) : fwd[p][q] = notsent
  /\ \E q \in Others(p) :
       fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroadcast, coordDecision, coordAlive,
                coordFaulty>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] # notsent
  /\ \A q \in Others(p) : fwd[p][q] = fwd[p][p]
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordAlive = FALSE
  /\ \A q \in participants : coordBroadcast[q] = undecided
  /\ \A q \in participants : \A r \in participants :
        (alive[q] /\ alive[r]) => fwd[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voteSent, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Next ==
  \/ \E p \in participants :
       SendRequest(p) \/ GetVote(p) \/ MakeDecision(p) \/ Broadcast(p)
         \/ Die(p) \/ SendVote(p) \/ AbortOnVote(p) \/ PreDecideFromCoord(p)
         \/ PreDecideFromForward(p) \/ Forward(p) \/ Decide(p)
         \/ AbortOnTimeout(p) \/ ParticipantDie(p)

\* Fairness: progress actions for both participants and the coordinator are
\* weakly fair (but death is not); this is what lets the reliable broadcast
\* eventually push every decision through to all non-faulty participants.
SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants :
       WF_vars(SendRequest(p)) /\ WF_vars(GetVote(p)) /\ WF_vars(MakeDecision(p))
         /\ WF_vars(Broadcast(p)) /\ WF_vars(SendVote(p))
         /\ WF_vars(AbortOnVote(p)) /\ WF_vars(PreDecideFromCoord(p))
         /\ WF_vars(PreDecideFromForward(p)) /\ WF_vars(Forward(p))
         /\ WF_vars(Decide(p)) /\ WF_vars(AbortOnTimeout(p))

TypeInvNB ==
  /\ vote \in [participants -> {undecided, yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordReq \in {waiting} \cup participants
  /\ coordVote \in {undecided, yes, no}
  /\ coordBroadcast \in [participants -> {undecided, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

\* AC3 is a safety property derived from the liveness condition; naming it
\* here helps TLC report the outcome of the non-blocking termination proof.
Properties == AC3

====