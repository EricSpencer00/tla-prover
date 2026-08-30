---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Atomic Commitment Protocol with Simple Broadcast: the coordinator collects
\* votes from participants and then broadcasts a commit/abort decision; a
\* crash mid-broadcast can leave participants undecided, so termination is
\* not guaranteed (the blocking case the spec was designed to admit).

VARIABLES vvote, valive, vdecided, vfaulty, vsent, casked, cvote,
          csent, cdecided, calive, cfaulty

vars == <<vvote, valive, vdecided, vfaulty, vsent, casked, cvote,
           csent, cdecided, calive, cfaulty>>

TypeInv ==
    /\ vvote \in [participants -> {yes, no}]
    /\ valive \in [participants -> BOOLEAN]
    /\ vdecided \in [participants -> {undecided, commit, abort}]
    /\ vfaulty \in [participants -> BOOLEAN]
    /\ vsent \in [participants -> BOOLEAN]
    /\ casked \in [participants -> BOOLEAN]
    /\ cvote \in [participants -> {yes, no, waiting}]
    /\ csent \in [participants -> {notsent, commit, abort}]
    /\ cdecided \in {undecided, commit, abort}
    /\ calive \in BOOLEAN
    /\ cfaulty \in BOOLEAN

Init ==
    /\ vvote \in [participants -> {yes, no}]
    /\ valive = [p \in participants |-> TRUE]
    /\ vdecided = [p \in participants |-> undecided]
    /\ vfaulty = [p \in participants |-> FALSE]
    /\ vsent = [p \in participants |-> FALSE]
    /\ casked = [p \in participants |-> FALSE]
    /\ cvote = [p \in participants |-> waiting]
    /\ csent = [p \in participants |-> notsent]
    /\ cdecided = undecided
    /\ calive = TRUE
    /\ cfaulty = FALSE

\* Coordinator actions.
SendReq(p) ==
    /\ calive
    /\ ~casked[p]
    /\ casked' = [casked EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vvote, valive, vdecided, vfaulty, vsent,
                   cvote, csent, cdecided, calive, cfaulty>>

ReceiveVote(p) ==
    /\ calive
    /\ cdecided = undecided
    /\ casked[p]
    /\ cvote[p] = waiting
    /\ vsent[p]
    /\ cvote' = [cvote EXCEPT ![p] = vvote[p]]
    /\ UNCHANGED <<vvote, valive, vdecided, vfaulty, vsent,
                   casked, csent, cdecided, calive, cfaulty>>

DetectFault(p) ==
    /\ calive
    /\ cdecided = undecided
    /\ casked[p]
    /\ cvote[p] = waiting
    /\ ~valive[p]
    /\ ~vsent[p]
    /\ cdecided' = abort
    /\ UNCHANGED <<vvote, valive, vdecided, vfaulty, vsent,
                   casked, cvote, csent, calive, cfaulty>>

MakeDecision ==
    /\ calive
    /\ cdecided = undecided
    /\ \A p \in participants : casked[p] /\ cvote[p] \in {yes, no}
    /\ cdecided' = IF \A p \in participants : cvote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vvote, valive, vdecided, vfaulty, vsent,
                   casked, cvote, csent, calive, cfaulty>>

\* Simple broadcast: the coordinator holds a per-participant send slot and
\* may be slow (or crash) before it gets around to it, leaving that
\* participant stuck -- which is the blocking case this spec admits.
BroadcastDecision(p) ==
    /\ calive
    /\ cdecided # undecided
    /\ csent[p] = notsent
    /\ csent' = [csent EXCEPT ![p] = cdecided]
    /\ UNCHANGED <<vvote, valive, vdecided, vfaulty, vsent,
                   casked, cvote, cdecided, calive, cfaulty>>

DieCoordinator ==
    /\ calive
    /\ calive' = FALSE
    /\ cfaulty' = TRUE
    /\ UNCHANGED <<vvote, valive, vdecided, vfaulty, vsent,
                   casked, cvote, csent, cdecided>>

\* Participant actions.
SendVote(p) ==
    /\ valive[p]
    /\ ~vsent[p]
    /\ casked[p]
    /\ vsent' = [vsent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vvote, valive, vdecided, vfaulty,
                   casked, cvote, csent, cdecided, calive, cfaulty>>

AbortOnVote(p) ==
    /\ valive[p]
    /\ vdecided[p] = undecided
    /\ vsent[p]
    /\ vvote[p] = no
    /\ vdecided' = [vdecided EXCEPT ![p] = abort]
    /\ UNCHANGED <<vvote, valive, vfaulty, vsent,
                   casked, cvote, csent, cdecided, calive, cfaulty>>

AbortTimeout(p) ==
    /\ valive[p]
    /\ vdecided[p] = undecided
    /\ ~casked[p]
    /\ cfaulty
    /\ vdecided' = [vdecided EXCEPT ![p] = abort]
    /\ UNCHANGED <<vvote, valive, vfaulty, vsent,
                   casked, cvote, csent, cdecided, calive, cfaulty>>

DecideOnCoord(p) ==
    /\ valive[p]
    /\ vdecided[p] = undecided
    /\ csent[p] # notsent
    /\ vdecided' = [vdecided EXCEPT ![p] = csent[p]]
    /\ UNCHANGED <<vvote, valive, vfaulty, vsent,
                   casked, cvote, csent, cdecided, calive, cfaulty>>

DieParticipant(p) ==
    /\ valive[p]
    /\ valive' = [valive EXCEPT ![p] = FALSE]
    /\ vfaulty' = [vfaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vvote, vdecided, vsent,
                   casked, cvote, csent, cdecided, calive, cfaulty>>

Next ==
    \/ \E p \in participants : SendReq(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ \E p \in participants : BroadcastDecision(p)
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortTimeout(p)
    \/ \E p \in participants : DecideOnCoord(p)
    \/ \E p \in participants : DieParticipant(p)
    \/ MakeDecision
    \/ DieCoordinator

\* SAFETY: agreement / consistency / validity / irrevocability.
Agreement ==
    \A p \in participants : \A q \in participants :
        (vdecided[p] = commit /\ vdecided[q] = abort) => FALSE

CommitValidity ==
    \A p \in participants : vdecided[p] = commit => (\A q \in participants : vvote[q] = yes)

AbortValidity ==
    \A p \in participants :
        vdecided[p] = abort =>
            (\E q \in participants : vvote[q] = no \/ vfaulty[q]) \/ cfaulty

Irrevocability ==
    \A p \in participants :
        /\ (vdecided[p] = commit => [q \in participants |-> vdecided[q]] = [q \in participants |-> IF q = p THEN commit ELSE vdecided[q]])
        /\ (vdecided[p] = abort => [q \in participants |-> vdecided[q]] = [q \in participants |-> IF q = p THEN abort ELSE vdecided[q]])

Spec == Init /\ [][Next]_vars
        /\ SF_vars(\E p \in participants : SendReq(p))
        /\ SF_vars(\E p \in participants : ReceiveVote(p))
        /\ SF_vars(\E p \in participants : DetectFault(p))
        /\ SF_vars(\E p \in participants : BroadcastDecision(p))
        /\ SF_vars(\E p \in participants : SendVote(p))
        /\ WF_vars(\E p \in participants : DecideOnCoord(p))
        /\ WF_vars(\E p \in participants : AbortTimeout(p))

\* LIVENESS: not guaranteed to reach decision (blocking), but guaranteed
\* to eventually resolve or reveal a fault.
EventualResolution ==
    <>(\A p \in participants : vdecided[p] # undecided) \/ cfaulty \/ (\E p \in participants : vfaulty[p])

====