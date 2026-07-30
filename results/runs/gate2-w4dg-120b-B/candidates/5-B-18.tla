---- MODULE W4DG_5m9p4t1 ----
EXTENDS Naturals

CONSTANTS participants

\* Simple Broadcast: a broadcast is a series of messages sent, so the
\* protocol "non-terminates" and the first broadcast of the final decision
\* may be lost.  The final decision still reaches every participant.

VARIABLES participant, coordinator

TypeInvParticipant == participant \in [
  participants -> [
    vote      : {"yes", "no"},
    alive     : BOOLEAN,
    decision  : {"undecided", "commit", "abort"},
    voteSent  : BOOLEAN
  ]
]

TypeInvCoordinator == coordinator \in [
  vote      : [participants -> {"waiting", "yes", "no"}],
  alive     : BOOLEAN,
  broadcast : [participants -> {"notsent", "commit", "abort"}],
  decision  : {"undecided", "commit", "abort"}
]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

\* Initial state: all alive, no decisions taken, no messages sent.

InitParticipant == participant \in [
  participants -> [
    vote     : {"yes"},
    alive    : TRUE,
    decision : "undecided",
    voteSent : FALSE
  ]
]

InitCoordinator == coordinator \in [
  vote      : [participants -> {"waiting"}],
  alive     : TRUE,
  broadcast : [participants -> {"notsent"}],
  decision  : "undecided"
]

Init == InitParticipant /\ InitCoordinator

\* COORDINATOR: request a vote from participant i

request(i) == /\ coordinator.alive
              /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = "waiting"]]
              /\ UNCHANGED participant

\* COORDINATOR: record the vote that participant i already sent

getVote(i) == /\ coordinator.alive
              /\ coordinator.vote[i] = "waiting"
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED participant

\* COORDINATOR: decide once all votes are in

makeDecision == /\ coordinator.alive
                /\ coordinator.decision = "undecided"
                /\ \A i \in participants : coordinator.vote[i] \in {"yes", "no"}
                /\ coordinator' = [coordinator EXCEPT !.decision =
                     IF \A i \in participants : coordinator.vote[i] = "yes"
                        THEN "commit" ELSE "abort"]
                /\ UNCHANGED participant

\* COORDINATOR: broadcast the decision to participant i

coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # "undecided"
                     /\ coordinator.broadcast[i] = "notsent"
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED participant

\* PARTICIPANT: send a vote to the coordinator

sendVote(i) == /\ participant[i].alive
               /\ ~participant[i].voteSent
               /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
               /\ UNCHANGED coordinator

\* PARTICIPANT: learn the decision from the coordinator

decide(i) == /\ coordinator.broadcast[i] # "notsent"
             /\ participant[i].decision = "undecided"
             /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
             /\ UNCHANGED coordinator

Prog == \E i \in participants : request(i) \/ getVote(i) \/ coordBroadcast(i) \/ sendVote(i)
         \/ makeDecision

Spec == Init /\ [][Prog]_<<coordinator, participant>>

\* SAFETY: participants that decide all reach the same decision

ABcast == [] \A i, j \in participants :
            \/ participant[i].decision # "commit"
            \/ participant[j].decision # "abort"

ABvote == [] (\E i \in participants : participant[i].decision = "commit")
           => \A j \in participants : participant[j].vote = "yes"

ABabort == [] (\E i \in participants : participant[i].decision = "abort")
            => \/ \E j \in participants : participant[j].vote = "no"
               \/ participant[i].faulty

ABdecision == [] /\ (\A i \in participants : participant[i].decision = "commit"
                          => [] (participant[i].decision = "commit"))
                  /\ (\A i \in participants : participant[i].decision = "abort"
                          => [] (participant[i].decision = "abort"))

\* LIVENESS: the decision is eventually reached (or a participant fails)

AFinish == <> \E i \in participants : participant[i].decision \in {"commit", "abort"}

====