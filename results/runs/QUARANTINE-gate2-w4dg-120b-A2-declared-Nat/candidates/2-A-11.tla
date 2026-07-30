---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinator state is identical to the base simple broadcast protocol (ACP-SB);
\* participants additionally keep a forwarding table per peer.
VARIABLES participantVote, participantAlive, participantDecision, faulty,
         participantVoted, coordReqMsg, coordVoteMsg, coordBroadcast,
         coordDecision, coordAlive, coordFaulty, fwdTable

vars == << participantVote, participantAlive, participantDecision, faulty,
            participantVoted, coordReqMsg, coordVoteMsg, coordBroadcast,
            coordDecision, coordAlive, coordFaulty, fwdTable >>

Clients == participants

TypeInvNB ==
    /\ participantVote \in [participants -> {yes, no, undecided}]
    /\ participantAlive \subseteq participants
    /\ participantDecision \in [participants -> {commit, abort, undecided}]
    /\ faulty \subseteq participants
    /\ participantVoted \subseteq participants
    /\ coordReqMsg \in {waiting, yes, no}
    /\ coordVoteMsg \in [participants -> {yes, no, undecided}]
    /\ coordBroadcast \in [participants -> {commit, abort, undecided}]
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordAlive \subseteq participants
    /\ coordFaulty \subseteq participants
    /\ fwdTable \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ participantVote = [p \in participants |-> undecided]
    /\ participantAlive = participants
    /\ participantDecision = [p \in participants |-> undecided]
    /\ faulty = {}
    /\ participantVoted = {}
    /\ coordReqMsg = waiting
    /\ coordVoteMsg = [p \in participants |-> undecided]
    /\ coordBroadcast = [p \in participants |-> undecided]
    /\ coordDecision = undecided
    /\ coordAlive = participants
    /\ coordFaulty = {}
    /\ fwdTable = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions: send request, collect votes, detect faults, decide, broadcast.
CoordinatorStep ==
    \/ /\ coordReqMsg = waiting
       /\ coordReqMsg' = no
       /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                      faulty, participantVoted, coordVoteMsg, coordBroadcast,
                      coordDecision, coordAlive, coordFaulty, fwdTable >>
    \/ /\ coordReqMsg = no
       /\ coordReqMsg' = yes
       /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                      faulty, participantVoted, coordVoteMsg, coordBroadcast,
                      coordDecision, coordAlive, coordFaulty, fwdTable >>
    \/ /\ coordReqMsg # waiting
       /\ coordVoteMsg' = [p \in participants |-> participantVote[p]]
       /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                      faulty, participantVoted, coordReqMsg, coordBroadcast,
                      coordDecision, coordAlive, coordFaulty, fwdTable >>
    /\ /\ coordAlive \cup coordFaulty = participants
       /\ Cardinality(coordFaulty) < Cardinality(participants)
       /\ \E p \in participants :
            /\ p \in coordAlive
            /\ /\ coordFaulty' = coordFaulty \cup {p}
               /\ coordAlive' = coordAlive \ {p}
    /\ /\ coordDecision = undecided
       /\ coordDecision' = IF \A p \in participants : coordVoteMsg[p] = yes
                            THEN commit ELSE abort
       /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                      faulty, participantVoted, coordReqMsg, coordVoteMsg,
                      coordBroadcast, coordAlive, coordFaulty, fwdTable >>
    /\ /\ coordDecision # undecided
       /\ coordBroadcast' = [p \in participants |-> coordDecision]
       /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                      faulty, participantVoted, coordReqMsg, coordVoteMsg,
                      coordDecision, coordAlive, coordFaulty, fwdTable >>
    /\ /\ coordAlive = {}
       /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                      faulty, participantVoted, coordReqMsg, coordVoteMsg,
                      coordBroadcast, coordDecision, coordAlive, coordFaulty,
                      fwdTable >>

\* Participant actions: a vote in the voting phase, abort on vote/no coordinator
\* message, abort on timeout, and the new reliable-broadcast actions.
ParticipantStep ==
    \/ \E p \in participants :
         /\ p \in participantAlive
         /\ participantVote[p] = undecided
         /\ participantVote' = [participantVote EXCEPT ![p] = yes]
         /\ participantVoted' = participantVoted \cup {p}
         /\ UNCHANGED << participantAlive, participantDecision, faulty,
                        coordReqMsg, coordVoteMsg, coordBroadcast, coordDecision,
                        coordAlive, coordFaulty, fwdTable >>
    \/ \E p \in participants :
         /\ p \in participantAlive
         /\ coordDecision = abort
         /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
         /\ UNCHANGED << participantVote, participantAlive, faulty,
                        participantVoted, coordReqMsg, coordVoteMsg, coordBroadcast,
                        coordDecision, coordAlive, coordFaulty, fwdTable >>
    \/ \E p \in participants :
         /\ p \in participantAlive
         /\ coordReqMsg = waiting
         /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
         /\ UNCHANGED << participantVote, participantAlive, faulty,
                        participantVoted, coordReqMsg, coordVoteMsg, coordBroadcast,
                        coordDecision, coordAlive, coordFaulty, fwdTable >>
    \/ \E p \in participants :
         /\ p \in participantAlive
         /\ participantDecision[p] = undecided
         /\ coordBroadcast[p] # undecided
         /\ fwdTable[p][p] = notsent
         /\ fwdTable' = [fwdTable EXCEPT ![p][p] = coordBroadcast[p]]
         /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                        faulty, participantVoted, coordReqMsg, coordVoteMsg,
                        coordBroadcast, coordDecision, coordAlive, coordFaulty >>
    \/ \E p \in participants :
         /\ p \in participantAlive
         /\ participantDecision[p] = undecided
         /\ \E q \in participants : fwdTable[q][p] # notsent
         /\ fwdTable[p][p] = notsent
         /\ fwdTable' = [fwdTable EXCEPT ![p][p] = fwdTable[q][p]]
         /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                        faulty, participantVoted, coordReqMsg, coordVoteMsg,
                        coordBroadcast, coordDecision, coordAlive, coordFaulty >>
    \/ \E p \in participants :
         /\ p \in participantAlive
         /\ fwdTable[p][p] # notsent
         /\ \E q \in participants : q # p /\ fwdTable[p][q] = notsent
         /\ fwdTable' = [fwdTable EXCEPT ![p][q] = fwdTable[p][p]]
         /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                        faulty, participantVoted, coordReqMsg, coordVoteMsg,
                        coordBroadcast, coordDecision, coordAlive, coordFaulty >>
    \/ \E p \in participants :
         /\ p \in participantAlive
         /\ participantDecision[p] = undecided
         /\ \A q \in participants : q # p => fwdTable[p][q] # notsent
         /\ participantDecision' = [participantDecision EXCEPT ![p] = fwdTable[p][p]]
         /\ UNCHANGED << participantVote, participantAlive, faulty,
                        participantVoted, coordReqMsg, coordVoteMsg,
                        coordBroadcast, coordDecision, coordAlive, coordFaulty,
                        fwdTable >>
    \/ \E p \in participants :
         /\ p \in participantAlive
         /\ participantDecision[p] = undecided
         /\ coordAlive = {}
         /\ \A q \in participants : coordBroadcast[q] = undecided
         /\ \A q \in participants :
              \A r \in participants : r \in {p, coordFaulty} => fwdTable[r][q] = notsent
         /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
         /\ UNCHANGED << participantVote, participantAlive, faulty,
                        participantVoted, coordReqMsg, coordVoteMsg,
                        coordBroadcast, coordDecision, coordAlive, coordFaulty,
                        fwdTable >>
    \/ \E p \in participants :
         /\ p \in participantAlive
         /\ participantAlive' = participantAlive \ {p}
         /\ faulty' = faulty \cup {p}
         /\ UNCHANGED << participantVote, participantDecision, coordReqMsg,
                        coordVoteMsg, coordBroadcast, coordDecision,
                        coordAlive, coordFaulty, fwdTable >>

Next == CoordinatorStep \/ ParticipantStep

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CoordinatorStep)
    /\ WF_vars(ParticipantStep)

\* No two participants reach different decisions.
AC1 == \A p \in participants : participantDecision[p] = commit => \A q \in participants : participantDecision[q] = commit

AC2 == \E p \in participants : participantDecision[p] = commit => \A q \in participants : participantVote[q] = yes

AC3 == \E p \in participants : participantDecision[p] = abort => (Cardinality({q \in participants : participantVote[q] = no}) > 0 \/ Cardinality(faulty) > 0 \/ Cardinality(coordFaulty) > 0)

AC4 == \A p \in participants : (participantDecision[p] = commit \/ participantDecision[p] = abort) ~> participantDecision[p]

\* Once the coordinator crashes and no broadcast was received, every non-faulty
\* participant decides on its own.
AC5 == \A p \in participants : (p \in participantAlive /\ participantDecision[p] = undecided) ~> (participantDecision[p] # undecided \/ p \in faulty \/ Cardinality(coordFaulty) > 0)

====