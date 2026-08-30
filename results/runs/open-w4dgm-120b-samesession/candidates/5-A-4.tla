---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinator and participants both collect votes and both may crash.
\* The "nondet" vote chooser lets each participant start with yes or no.
\* Simple broadcast sends the decision to one participant at a time; a
\* coordinator crash mid-broadcast can leave others undecided (blocking).

VARIABLES coordAlive, coordFaulty, voted, coordDecision, coordVoted,
          coordSent, pAlive, pFaulty, pVote, pDecided

Vars == <<coordAlive, coordFaulty, voted, coordDecision, coordVoted,
          coordSent, pAlive, pFaulty, pVote, pDecided>>

TypeOK ==
    /\ coordAlive \in BOOLEAN /\ coordFaulty \in BOOLEAN
    /\ voted \subseteq participants
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordVoted \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {commit, abort, notsent}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> {yes, no}]
    /\ pDecided \in [participants -> {commit, abort, undecided}]

Init ==
    /\ coordAlive = TRUE /\ coordFaulty = FALSE
    /\ voted = {}
    /\ coordDecision = undecided
    /\ coordVoted = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pVote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
    /\ pDecided = [p \in participants |-> undecided]

\* Coordinator actions.
SendReq(p) ==
    /\ coordAlive /\ coordSent[p] = notsent
    /\ coordDecision = undecided
    /\ (p \notin voted) => coordSent' = [coordSent EXCEPT ![p] = notsent]
    /\ coordVoted' = [coordVoted EXCEPT ![p] = waiting]
    /\ UNCHANGED <<coordAlive, coordFaulty, voted, coordDecision,
                    pAlive, pFaulty, pVote, pDecided>>

ReceiveVote(p) ==
    /\ coordAlive /\ coordDecision = undecided
    /\ p \in voted /\ coordVoted[p] = waiting
    /\ coordVoted' = [coordVoted EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, voted, coordDecision,
                    coordSent, pAlive, pFaulty, pVote, pDecided>>

DetectPFail(p) ==
    /\ coordAlive /\ coordDecision = undecided
    /\ p \notin voted /\ coordVoted[p] = waiting
    /\ ~pAlive /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, voted, coordVoted,
                    coordSent, pAlive, pFaulty, pVote, pDecided>>

MakeDecision ==
    /\ coordAlive /\ coordDecision = undecided
    /\ \A p \in participants: p \in voted
    /\ coordDecision' = IF \A p \in participants: coordVoted[p] = yes
                        THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, voted, coordVoted,
                    coordSent, pAlive, pFaulty, pVote, pDecided>>

Broadcast(p) ==
    /\ coordAlive /\ coordDecision \in {commit, abort}
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, voted, coordDecision,
                    coordVoted, pAlive, pFaulty, pVote, pDecided>>

CoordDie ==
    /\ coordAlive /\ coordAlive' = FALSE /\ coordFaulty' = TRUE
    /\ UNCHANGED <<voted, coordDecision, coordVoted, coordSent,
                    pAlive, pFaulty, pVote, pDecided>>

\* Participant actions.
SendVote(p) ==
    /\ pAlive /\ p \notin voted
    /\ voted' = voted \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVoted,
                    coordSent, pAlive, pFaulty, pVote, pDecided>>

AbortByVote(p) ==
    /\ pAlive /\ p \notin voted /\ pVote[p] = no /\ pDecided[p] = undecided
    /\ pDecided' = [pDecided EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, voted, coordDecision,
                    coordVoted, coordSent, pAlive, pFaulty, pVote>>

AbortReqTimeout(p) ==
    /\ pAlive /\ p \notin voted /\ ~coordAlive /\ pDecided[p] = undecided
    /\ pDecided' = [pDecided EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, voted, coordDecision,
                    coordVoted, coordSent, pAlive, pFaulty, pVote>>

Decide(p) ==
    /\ pAlive /\ coordSent[p] \in {commit, abort}
    /\ pDecided[p] = undecided
    /\ pDecided' = [pDecided EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, voted, coordDecision,
                    coordVoted, coordSent, pAlive, pFaulty, pVote>>

PDie(p) ==
    /\ pAlive /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
                          /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, voted, coordDecision,
                    coordVoted, coordSent, pVote, pDecided>>

CoordAct == SendReq("p1") \/ ReceiveVote("p1") \/ DetectPFail("p1")
             \/ Broadcast("p1") \/ CoordDie
CoordAct == CoordAct \/ SendReq("p2") \/ ReceiveVote("p2")
             \/ DetectPFail("p2") \/ Broadcast("p2")
CoordAct == CoordAct \/ SendReq("p3") \/ ReceiveVote("p3")
             \/ DetectPFail("p3") \/ Broadcast("p3")
CoordAct == CoordAct \/ MakeDecision

PAct == \E p \in participants:
            SendVote(p) \/ AbortByVote(p) \/ AbortReqTimeout(p) \/ Decide(p) \/ PDie(p)

Next == CoordAct \/ PAct

\* SAFETY: no contradictory outcomes; progress is accounted for by votes and
\* failures, not by the broadcast itself (which is what makes AC5 fail).
Spec == Init /\ [][Next]_Vars
        /\ WF_Vars(PAct)
        /\ WF_Vars(CoordAct)

\* None of two participants decided differently.
Agree ==
    \A p1, p2 \in participants:
        ~ (pDecided[p1] = commit /\ pDecided[p2] = abort)

\* Commit only when every vote was yes.
CommitValid == \A p \in participants: pDecided[p] = commit => \A q \in participants: coordVoted[q] = yes

\* Abort only when some vote was no, or someone is faulty.
AbortValid == \A p \in participants: pDecided[p] = abort =>
    (\E q \in participants: coordVoted[q] = no) \/ (\E q \in participants: pFaulty[q] \/ coordFaulty)

\* Decision is one-way: decided participants never flip.
Irreversible ==
    \A p \in participants:
        /\ (pDecided[p] = commit => pDecided' [p] = commit)
        /\ (pDecided[p] = abort => pDecided' [p] = abort)

EventualDecide == <>(\E p \in participants: pDecided[p] # undecided)

====