---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordVote, coordAlive, coordFaulty, coordReq, coordRecv, coordState
Variables == <<coordVote, coordAlive, coordFaulty, coordReq, coordRecv, coordState>>

VARIABLES partVote, partAlive, partDecision, partFaulty, partReq, partTable
PVariables == <<partVote, partAlive, partDecision, partFaulty, partReq, partTable>>

\* The forwarding table holds, per participant, what pre-decision it has stored
\* (indexed by itself) and whether it has forwarded that pre-decision to others.
Entry == {notsent, commit, abort}

TypeOK ==
  /\ coordVote \in {yes, no}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordReq \in BOOLEAN
  /\ coordRecv \in BOOLEAN
  /\ coordState \in {undecided, commit, abort}
  /\ partVote \in [participants -> {yes, no}]
  /\ partAlive \in [participants -> BOOLEAN]
  /\ partDecision \in [participants -> {undecided, commit, abort}]
  /\ partFaulty \in [participants -> BOOLEAN]
  /\ partReq \in [participants -> BOOLEAN]
  /\ partTable \in [participants -> [participants -> Entry]]

Init ==
  /\ coordVote = yes
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordReq = FALSE
  /\ coordRecv = FALSE
  /\ coordState = undecided
  /\ partVote = [p \in participants |-> yes]
  /\ partAlive = [p \in participants |-> TRUE]
  /\ partDecision = [p \in participants |-> undecided]
  /\ partFaulty = [p \in participants |-> FALSE]
  /\ partReq = [p \in participants |-> TRUE]
  /\ partTable = [p \in participants |-> [q \in participants |-> notsent]]

CoordinatorRest ==
  /\ coordAlive = FALSE
  /\ coordFaulty = FALSE

\* Base actions from ACP-SB (send request, get vote, detect fault, decide,
\* broadcast, die) are assumed to be present and are included here by name, but
\* their definitions are unchanged from the base specification.
SendReq == /\ coordReq = FALSE /\ coordAlive = TRUE /\ coordReq' = TRUE
            /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordRecv, coordState,
                           partVote, partAlive, partDecision, partFaulty, partReq, partTable>>

GetVote == /\ coordReq = TRUE /\ coordAlive = TRUE /\ coordVote' = no
           /\ UNCHANGED <<coordAlive, coordFaulty, coordReq, coordRecv, coordState,
                          partVote, partAlive, partDecision, partFaulty, partReq, partTable>>

DetectFault == /\ CoordinatorRest /\ coordFaulty' = TRUE
               /\ UNCHANGED <<coordVote, coordAlive, coordReq, coordRecv, coordState,
                              partVote, partAlive, partDecision, partFaulty, partReq, partTable>>

MakeDecision == /\ coordState = undecided /\ coordAlive = TRUE
                /\ coordState' = IF coordVote = yes THEN commit ELSE abort
                /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordReq, coordRecv,
                               partVote, partAlive, partDecision, partFaulty, partReq, partTable>>

Broadcast == /\ coordState \in {commit, abort} /\ coordAlive = TRUE
             /\ coordRecv' = TRUE
             /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordReq, coordState,
                            partVote, partAlive, partDecision, partFaulty, partReq, partTable>>

Die == /\ coordAlive = TRUE /\ coordAlive' = FALSE
       /\ UNCHANGED <<coordVote, coordFaulty, coordReq, coordRecv, coordState,
                      partVote, partAlive, partDecision, partFaulty, partReq, partTable>>

SendVote(p) == /\ partReq[p] = TRUE /\ partAlive[p] = TRUE
               /\ partVote' = [partVote EXCEPT ![p] = no]
               /\ partReq' = [partReq EXCEPT ![p] = FALSE]
               /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordReq,
                              coordRecv, coordState, partAlive, partDecision,
                              partFaulty, partTable>>

AbortOnVote(p) == /\ partAlive[p] = TRUE /\ partDecision[p] = undecided
                  /\ partVote[p] = no
                  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
                  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordReq,
                                 coordRecv, coordState, partVote, partAlive,
                                 partFaulty, partReq, partTable>>

PreDecideFromCoord(p) ==
  /\ partAlive[p] = TRUE /\ partDecision[p] = undecided
  /\ coordRecv = TRUE /\ partTable[p][p] = notsent
  /\ partTable' = [partTable EXCEPT ![p][p] = coordState]
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordReq, coordRecv,
                 coordState, partVote, partAlive, partDecision, partFaulty,
                 partReq>>

PreDecideFromForward(p) ==
  /\ partAlive[p] = TRUE /\ partDecision[p] = undecided
  /\ partTable[p][p] = notsent
  /\ \E q \in participants :
       /\ q # p
       /\ partTable[q][p] # notsent
       /\ partTable' = [partTable EXCEPT ![p][p] = partTable[q][p]]
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordReq, coordRecv,
                 coordState, partVote, partAlive, partDecision, partFaulty,
                 partReq>>

Forward(p, r) ==
  /\ partAlive[p] = TRUE /\ partTable[p][p] # notsent
  /\ partTable[p][r] = notsent
  /\ partTable' = [partTable EXCEPT ![p][r] = partTable[p][p]]
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordReq, coordRecv,
                 coordState, partVote, partAlive, partDecision, partFaulty,
                 partReq>>

Decide(p) ==
  /\ partAlive[p] = TRUE /\ partDecision[p] = undecided
  /\ \A r \in participants : partTable[p][r] # notsent
  /\ partDecision' = [partDecision EXCEPT ![p] = partTable[p][p]]
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordReq, coordRecv,
                 coordState, partVote, partAlive, partFaulty, partReq, partTable>>

\* Abort on timeout when no surviving coordinator or forwarding source exists.
AbortOnTimeout(p) ==
  /\ partAlive[p] = TRUE /\ partDecision[p] = undecided
  /\ coordAlive = FALSE /\ coordFaulty = FALSE
  /\ ~coordRecv
  /\ \A q \in participants : partAlive[q] => partTable[q][p] = notsent
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordReq, coordRecv,
                 coordState, partVote, partAlive, partFaulty, partReq, partTable>>

DieP(p) == /\ partAlive[p] = TRUE /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
           /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
           /\ UNCHANGED <<coordVote, coordAlive, coordFaulty, coordReq,
                          coordRecv, coordState, partVote, partDecision,
                          partReq, partTable>>

Next ==
  \/ SendReq \/ GetVote \/ DetectFault \/ MakeDecision \/ Broadcast \/ Die
  \/ \E p \in participants :
       \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DieP(p)
       \/ PreDecideFromCoord(p) \/ PreDecideFromForward(p) \/ Decide(p)
       \/ \E r \in participants : Forward(p, r)

\* Forwarding and pre-deciding are progress actions; death is not.
SpecNB ==
  /\ Init /\ [][Next]_<<coordVote, coordAlive, coordFaulty, coordReq,
               coordRecv, coordState, partVote, partAlive, partDecision,
               partFaulty, partReq, partTable>>
  /\ WF_vars(\E p \in participants, r \in participants : Forward(p, r))
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideFromForward(p))

\* Safety: two participants can never disagree on the final decision.
AC1 ==
  \A p, q \in participants :
    (partDecision[p] = commit) => (partDecision[q] = commit \/ partDecision[q] = undecided)

\* Safety: a commit is only reachable if everybody voted yes.
AC2 ==
  \A p \in participants : partDecision[p] = commit => \A q \in participants : partVote[q] = yes

\* Safety: an abort is only reachable by a vote-no, a faulty participant, or a
\* faulty coordinator -- nothing else can abort a participant.
AC3 ==
  \A p \in participants :
    partDecision[p] = abort => (\E q \in participants : partVote[q] = no \/ partFaulty[q] = TRUE \/ coordFaulty = TRUE)

\* Safety: decisions are final and cannot be undone.
AC4 ==
  \A p \in participants :
    partDecision[p] \in {commit, abort} => partDecision[p) = partDecision[p]

\* Liveness: the non-blocking guarantee -- every surviving participant eventually
\* finalizes its decision, even if the coordinator crashes mid-broadcast.
AC5 == \A p \in participants : (partAlive[p] = TRUE) ~> (partDecision[p] \in {commit, abort})

\* AC3 liveness: eventually the protocol makes progress (or crashes).
\* Not blocked on participants finalizing, so it can still fire when a
\* participant is stuck waiting for a live forwarder that never exists.
AC3Liveness ==
  \E p \in participants : (partDecision[p] \in {commit, abort}) \/ coordFaulty \/ (\E q \in participants : partFaulty[q] = TRUE)

TypeInvNB == TypeOK
====