---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS
    participants,
    yes,
    no,
    undecided,
    commit,
    abort,
    waiting,
    notsent

VARIABLES
    vote,
    alive,
    decision,
    faulty,
    sent,
    coordSent,
    coordVote,
    coordBroadcast,
    coordDecision,
    coordAlive,
    coordFaulty

vars == <<vote, alive, decision, faulty, sent, coordSent, coordVote,
           coordBroadcast, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in BOOLEAN
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in BOOLEAN
    /\ sent \subseteq participants
    /\ coordSent \in [participants -> BOOLEAN]
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordBroadcast \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ \E v \in [participants -> {yes, no}]:
         vote = v
    /\ alive = TRUE
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = FALSE
    /\ sent = {}
    /\ coordSent = [p \in participants |-> FALSE]
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordBroadcast = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

CoordSendRequest(p) ==
    /\ coordAlive
    /\ ~coordSent[p]
    /\ coordSent' = [coordSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordSent[p]
    /\ coordVote[p] = waiting
    /\ p \in sent
    /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordSent,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordSent[p]
    /\ coordVote[p] = waiting
    /\ ~alive
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordSent,
                   coordVote, coordBroadcast, coordAlive, coordFaulty>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: coordVote[p] \in {yes, no}
    /\ coordDecision' = IF \A p \in participants: coordVote[p] = yes
                          THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordSent,
                   coordVote, coordBroadcast, coordAlive, coordFaulty>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordBroadcast[p] = notsent
    /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordSent,
                   coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordSent,
                   coordVote, coordBroadcast, coordDecision, coordFaulty>>

PartSendVote(p) ==
    /\ alive
    /\ p \notin sent
    /\ coordSent[p]
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<vote, alive, decision, faulty, coordSent, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PartAbortOnVote(p) ==
    /\ alive
    /\ decision[p] = undecided
    /\ p \in sent
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordSent, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PartAbortOnTimeout(p) ==
    /\ alive
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~coordSent[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordSent, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PartDecideOnBroadcast(p) ==
    /\ alive
    /\ decision[p] = undecided
    /\ coordBroadcast[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = coordBroadcast[p]]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordSent, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
    /\ alive
    /\ alive' = FALSE
    /\ faulty' = TRUE
    /\ UNCHANGED <<vote, decision, sent, coordSent, coordVote,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

CoordProgress ==
    \/ \E p \in participants: CoordSendRequest(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordMakeDecision
    \/ CoordDie

PartProgress ==
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnVote(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideOnBroadcast(p)

Next ==
    \/ CoordProgress
    \/ PartProgress
    \/ \E p \in participants: PartDie(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(CoordProgress)
        /\ \A p \in participants: WF_vars(PartProgress)

NoDoubleDecision == \A p, q \in participants: (decision[p] = commit /\ decision[q] = abort) => p = q

CommitValidity == \A p \in participants: decision[p] = commit => \A q \in participants: vote[q] = yes

AbortValidity == \A p \in participants: decision[p] = abort =>
                    (\E q \in participants: vote[q] = no) \/ faulty \/ coordFaulty

Irrevocability == \A p \in participants: (decision[p] = commit \/ decision[p] = abort) ~=>
                    (decision[p] = commit \/ decision[p] = abort)

Decide == \A p \in participants: decision[p] # undecided

EventuallyDecideOrFault ==
    (Decide \/ faulty \/ coordFaulty)
        ~> (Decide \/ faulty \/ coordFaulty)

====