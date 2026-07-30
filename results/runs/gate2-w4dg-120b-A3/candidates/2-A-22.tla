---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordinator, participant, decision, alive, faulty, voteSent, forwardTable

TypeInvNB ==
    /\ coordinator \in [request \in {waiting, yes, no}, vote \in {yes, no, none},
                        broadcast \in [participants -> {notsent, commit, abort}],
                        decision \in {undecided, commit, abort}, alive \in BOOLEAN, faulty \in BOOLEAN]
    /\ participant \in [participants -> [vote \in {unset, yes, no}, decision \in {undecided, commit, abort},
                                         alive \in BOOLEAN, faulty \in BOOLEAN]]
    /\ voteSent \in BOOLEAN
    /\ forwardTable \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ coordinator = [request |-> waiting, vote |-> none, broadcast |-> [p \in participants |-> notsent],
                      decision |-> undecided, alive |-> TRUE, faulty |-> FALSE]
    /\ participant = [p \in participants |-> [vote |-> unset, decision |-> undecided, alive |-> TRUE,
                                              faulty |-> FALSE]]
    /\ voteSent = FALSE
    /\ forwardTable = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
    /\ coordinator.alive /\ ~coordinator.faulty /\ coordinator.request = waiting
    /\ coordinator' = [coordinator EXCEPT !.request = yes]
    /\ UNCHANGED <<participant, decision, alive, faulty, voteSent, forwardTable>>

GetVote ==
    /\ coordinator.alive /\ ~coordinator.faulty /\ coordinator.request = yes /\ ~voteSent
    /\ coordinator' = [coordinator EXCEPT !.vote = yes]
    /\ voteSent' = TRUE
    /\ UNCHANGED <<participant, decision, alive, faulty, forwardTable>>

DetectFault ==
    /\ coordinator.alive /\ coordinator.request = waiting /\ coordinator.vote # none /\ coordinator.vote = no
    /\ coordinator' = [coordinator EXCEPT !.vote = no]
    /\ UNCHANGED <<participant, decision, alive, faulty, voteSent, forwardTable>>

SendVote(p) ==
    /\ participant[p].alive /\ participant[p].vote = unset /\ coordinator.vote = yes
    /\ participant' = [participant EXCEPT ![p].vote = yes]
    /\ UNCHANGED <<coordinator, decision, alive, faulty, voteSent, forwardTable>>

AbortOnVote(p) ==
    /\ participant[p].alive /\ participant[p].vote = unset /\ coordinator.vote = no
    /\ participant' = [participant EXCEPT ![p].vote = no]
    /\ UNCHANGED <<coordinator, decision, alive, faulty, voteSent, forwardTable>>

AbortOnTimeout(p) ==
    /\ participant[p].alive /\ participant[p].decision = undecided
    /\ ~coordinator.alive
    /\ \A q \in participants : coordinator.broadcast[q] = notsent
    /\ \A q \in participants : participant[q].alive => \A r \in participants : forwardTable[q][r] = notsent
    /\ participant' = [participant EXCEPT ![p].decision = abort]
    /\ UNCHANGED <<coordinator, decision, alive, faulty, voteSent, forwardTable>>

BroadcastDecision ==
    /\ coordinator.alive /\ ~coordinator.faulty /\ coordinator.vote # none /\ coordinator.decision = undecided
    /\ coordinator' = [coordinator EXCEPT !.decision = coordinator.vote,
                        !.broadcast = [p \in participants |-> coordinator.vote]]
    /\ UNCHANGED <<participant, decision, alive, faulty, voteSent, forwardTable>>

PreDecideFromCoordinator(p) ==
    /\ participant[p].alive
    /\ participant[p].decision = undecided
    /\ forwardTable[p][p] = notsent
    /\ coordinator.broadcast[p] # notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = coordinator.broadcast[p]]
    /\ UNCHANGED <<coordinator, participant, decision, alive, faulty, voteSent>>

PreDecideFromForward(p) ==
    /\ participant[p].alive
    /\ participant[p].decision = undecided
    /\ forwardTable[p][p] = notsent
    /\ \E q \in participants : forwardTable[q][p] # notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][p] = CHOOSE ft \in {commit, abort} :
                            \E q \in participants : forwardTable[q][p] # notsent /\ ft = forwardTable[q][p]]
    /\ UNCHANGED <<coordinator, participant, decision, alive, faulty, voteSent>>

Forward(p, q) ==
    /\ participant[p].alive
    /\ forwardTable[p][p] # notsent
    /\ forwardTable[p][q] = notsent
    /\ forwardTable' = [forwardTable EXCEPT ![p][q] = forwardTable[p][p]]
    /\ UNCHANGED <<coordinator, participant, decision, alive, faulty, voteSent>>

Decide(p) ==
    /\ participant[p].alive
    /\ participant[p].decision = undecided
    /\ \A q \in participants : forwardTable[p][q] # notsent
    /\ participant' = [participant EXCEPT ![p].decision = forwardTable[p][p]]
    /\ UNCHANGED <<coordinator, decision, alive, faulty, voteSent, forwardTable>>

Die ==
    /\ coordinator.alive
    /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
    /\ UNCHANGED <<participant, decision, alive, faulty, voteSent, forwardTable>>

Next ==
    \/ SendRequest \/ GetVote \/ DetectFault \/ BroadcastDecision \/ Die
    \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ PreDecideFromCoordinator(p)
                              \/ PreDecideFromForward(p) \/ Decide(p)
    \/ \E p, q \in participants : Forward(p, q)

SpecNB ==
    /\ Init
    /\ [][Next]_<<coordinator, participant, decision, alive, faulty, voteSent, forwardTable>>
    /\ WF_vars(SendVote("p1"))
    /\ WF_vars(PreDecideFromCoordinator("p1"))
    /\ WF_vars(PreDecideFromForward("p1"))
    /\ WF_vars(Forward("p1", "p2"))
    /\ WF_vars(Decide("p1"))
    /\ WF_vars(SendRequest)
    /\ WF_vars(GetVote) /\ WF_vars(DetectFault) /\ WF_vars(BroadcastDecision)

AC1 ==
    \A p1, p2 \in participants :
        (participant[p1].decision = commit /\ participant[p2].decision = abort) => FALSE

AC2 ==
    \E p \in participants : participant[p].decision = commit =>
        \A q \in participants : participant[q].vote = yes

AC3 ==
    \E p \in participants : participant[p].decision = abort =>
        \/ \E q \in participants : participant[q].vote = no
        \/ \E q \in participants : participant[q].faulty
        \/ coordinator.faulty

AC4 ==
    \A p \in participants :
        (participant[p].decision = commit \/ participant[p].decision = abort) =>
            (participant[p].decision = (IF coordinator.decision = commit THEN commit ELSE abort))

AC5 == (\A p \in participants : (participant[p].alive => (participant[p].decision = commit \/ participant[p].decision = abort)))
====