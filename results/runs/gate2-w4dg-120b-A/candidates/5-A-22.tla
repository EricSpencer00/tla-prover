---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pref, alive, decision, faulty, sent, coordReq, coordVote,
         coordSent, coordDecision, coordAlive, coordFaulty

vars == <<pref, alive, decision, faulty, sent, coordReq, coordVote,
          coordSent, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ pref \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sent \in [participants -> BOOLEAN]
    /\ coordReq \in [participants -> BOOLEAN]
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ pref \in [participants -> {yes, no}]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sent = [p \in participants |-> FALSE]
    /\ coordReq = [p \in participants |-> FALSE]
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

CoordSendRequest(p) ==
    /\ coordAlive
    /\ ~coordReq[p]
    /\ coordReq' = [coordReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pref, alive, decision, faulty, sent,
                  coordVote, coordSent, coordDecision,
                  coordAlive, coordFaulty>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : coordReq[q]
    /\ coordVote[p] = waiting
    /\ sent[p]
    /\ coordVote' = [coordVote EXCEPT ![p] = pref[p]]
    /\ UNCHANGED <<pref, alive, decision, faulty, sent,
                  coordReq, coordSent, coordDecision,
                  coordAlive, coordFaulty>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : coordReq[q]
    /\ coordVote[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<pref, alive, decision, faulty, sent,
                  coordReq, coordVote, coordSent,
                  coordAlive, coordFaulty>>

CoordDecide ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordVote[p] # waiting
    /\ coordDecision' = IF \A p \in participants : pref[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pref, alive, decision, faulty, sent,
                  coordReq, coordVote, coordSent,
                  coordAlive, coordFaulty>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<pref, alive, decision, faulty, sent,
                  coordReq, coordVote,
                  coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<pref, alive, decision, faulty, sent,
                  coordReq, coordVote, coordSent, coordDecision,
                  coordAlive>>

ParticipantSend(p) ==
    /\ alive[p]
    /\ coordReq[p]
    /\ ~sent[p]
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pref, alive, decision, faulty, coordReq,
                  coordVote, coordSent, coordDecision,
                  coordAlive, coordFaulty>>

ParticipantAbortOnNo(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sent[p]
    /\ pref[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pref, alive, faulty, sent, coordReq,
                  coordVote, coordSent, coordDecision,
                  coordAlive, coordFaulty>>

ParticipantAbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~coordReq[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pref, alive, faulty, sent, coordReq,
                  coordVote, coordSent, coordDecision,
                  coordAlive, coordFaulty>>

ParticipantDecideOnBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSent[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<pref, alive, faulty, sent, coordReq,
                  coordVote, coordSent, coordDecision,
                  coordAlive, coordFaulty>>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pref, decision, sent, coordReq, coordVote,
                  coordSent, coordDecision, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants : CoordSendRequest(p)
    \/ \E p \in participants : CoordReceiveVote(p)
    \/ \E p \in participants : CoordDetectFault(p)
    \/ CoordDecide
    \/ \E p \in participants : CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants : ParticipantSend(p)
    \/ \E p \in participants : ParticipantAbortOnNo(p)
    \/ \E p \in participants : ParticipantAbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDecideOnBroadcast(p)
    \/ \E p \in participants : ParticipantDie(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in participants : ParticipantSend(p))
        /\ WF_vars(\E p \in participants : ParticipantAbortOnNo(p))
        /\ WF_vars(\E p \in participants : ParticipantDecideOnBroadcast(p))
        /\ WF_vars(\E p \in participants : CoordBroadcast(p))
        /\ WF_vars(\E p \in participants : CoordDecide)

Agreement ==
    \A p \in participants, q \in participants :
        (decision[p] = commit) => (decision[q] # abort)

CommitValidity ==
    \A p \in participants :
        decision[p] = commit => (\A q \in participants : pref[q] = yes)

AbortValidity ==
    \A p \in participants :
        decision[p] = abort =>
            \/ \E q \in participants : pref[q] = no
            \/ \E q \in participants : faulty[q]
            \/ coordFaulty

Irreversibility ==
    \A p \in participants :
        /\ decision[p] = commit => (\A q \in participants : decision[q] # abort)
        /\ decision[p] = abort => (\A q \in participants : decision[q] # commit)

DecisionLiveness ==
    (\A p \in participants : decision[p] # undecided) \/ (\E q \in participants : faulty[q]) \/ coordFaulty

====