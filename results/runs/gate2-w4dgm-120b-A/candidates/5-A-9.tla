---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sent, coordAsked, coordVote,
          coordSent, coordDecision, coordAlive

vars == <<vote, alive, decision, faulty, sent, coordAsked,
           coordVote, coordSent, coordDecision, coordAlive>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sent \in [participants -> BOOLEAN]
    /\ coordAsked \in [participants -> BOOLEAN]
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {committed, notsent}]
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordAlive \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sent = [p \in participants |-> FALSE]
    /\ coordAsked = [p \in participants |-> FALSE]
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE

\* Simple broadcast: the coordinator sends one participant at a time, so a
\* failure mid-broadcast can leave others undecided.
CoordSendVoteRequest(p) ==
    /\ coordAlive
    /\ ~coordAsked[p]
    /\ coordAsked' = [coordAsked EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordVote,
                   coordSent, coordDecision, coordAlive>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordAsked[p]
    /\ coordVote[p] = waiting
    /\ sent[p]
    /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordAsked,
                   coordSent, coordDecision, coordAlive>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordAsked[p]
    /\ coordVote[p] = waiting
    /\ (~alive[p] /\ ~sent[p])
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordAsked,
                   coordVote, coordSent, coordAlive>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordAsked[p]
    /\ \A p \in participants : coordVote[p] # waiting
    /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes
                         THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordAsked,
                   coordVote, coordSent, coordAlive>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = committed]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordAsked,
                   coordVote, coordDecision, coordAlive>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ faulty' = [p \in participants |-> faulty[p] \cup {coordAlive}]
    /\ UNCHANGED <<vote, alive, decision, sent, coordAsked,
                   coordVote, coordSent, coordDecision>>

SendVote(p) ==
    /\ alive[p]
    /\ coordAsked[p]
    /\ ~sent[p]
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, coordAsked,
                   coordVote, coordSent, coordDecision, coordAlive>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sent[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordAsked,
                   coordVote, coordSent, coordDecision, coordAlive>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~coordAsked[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordAsked,
                   coordVote, coordSent, coordDecision, coordAlive>>

DecideFromCoordinator(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSent[p] = committed
    /\ decision' = [decision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordAsked,
                   coordVote, coordSent, coordDecision, coordAlive>>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sent, coordAsked,
                   coordVote, coordSent, coordDecision, coordAlive>>

Next ==
    \/ \E p \in participants :
        CoordSendVoteRequest(p) \/ CoordReceiveVote(p) \/ CoordDetectFault(p)
        \/ CoordBroadcast(p) \/ SendVote(p) \/ AbortOnVote(p)
        \/ AbortOnTimeout(p) \/ DecideFromCoordinator(p)
        \/ ParticipantDie(p)
    \/ CoordMakeDecision \/ CoordDie

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in participants : SF_vars(SendVote(p))
    /\ \A p \in participants : SF_vars(AbortOnVote(p))
    /\ \A p \in participants : SF_vars(DecideFromCoordinator(p))
    /\ WF_vars(CoordMakeDecision)

\* Safety: no two participants can ever decide differently.
Agreement ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValidity ==
    \A p \in participants :
        decision[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
    \A p \in participants :
        decision[p] = abort =>
            (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ (~coordAlive)

Irrevocable ==
    \A p \in participants :
        /\ (decision[p] = commit => [decision EXCEPT ![p] = commit] = decision[p])
        /\ (decision[p] = abort => [decision EXCEPT !p] = abort = decision[p])

\* Liveness: either everyone decides or some fault surfaces; termination is NOT
\* guaranteed under coordinator crash during broadcast.
EventualDecisionOrFault ==
    <>(\A p \in participants : decision[p] # undecided \/ \E q \in participants : faulty[q])

====