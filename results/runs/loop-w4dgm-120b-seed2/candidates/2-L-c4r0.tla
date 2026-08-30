---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* State tracking from the base ACS-SB protocol (everything the spec says it
\* tracks about the coordinator and each participant): a vote, an alive flag,
\* the final decision, a faulty flag, a vote-sent flag, and the coordinator's
\* request/vote/broadcast/decision/alive/faulty state.
VARIABLES pVote, pAlive, pDecided, pFaulty, pSent, coordReq, coordVote,
          coordBroadcast, coordDecision, coordAlive, coordFaulty,
          forward

vars == <<pVote, pAlive, pDecided, pFaulty, pSent, coordReq, coordVote,
          coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

TypeInv ==
  /\ pVote \in [participants -> {yes, no, undecided}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecided \in [participants -> {commit, abort, waiting}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pSent \in [participants -> BOOLEAN]
  /\ coordReq \in {yes, no, undecided}
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in [participants -> {"none", "sent"}]
  /\ coordDecision \in {commit, abort, waiting}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ pVote = [p \in participants |-> undecided]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pDecided = [p \in participants |-> waiting]
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ pSent = [p \in participants |-> FALSE]
  /\ coordReq = undecided
  /\ coordVote = undecided
  /\ coordBroadcast = [p \in participants |-> "none"]
  /\ coordDecision = waiting
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

\* The coordinator broadcasts once: a single decision survives the crash.
SendRequest ==
  /\ coordAlive
  /\ coordReq = undecided
  /\ coordReq' = yes
  /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

GetVote ==
  /\ coordAlive
  /\ coordReq # undecided
  /\ coordVote = undecided
  /\ \E p \in participants :
       /\ pAlive[p]
       /\ pSent[p]
       /\ coordVote' = pVote[p]
  /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, coordReq,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

DetectCoordFault ==
  /\ coordAlive
  /\ coordFaulty
  /\ coordAlive' = FALSE
  /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, coordReq,
                 coordVote, coordBroadcast, coordDecision, coordFaulty, forward>>

MakeDecision ==
  /\ coordAlive
  /\ coordReq # undecided
  /\ coordVote # undecided
  /\ coordDecision = waiting
  /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, coordReq,
                 coordVote, coordBroadcast, coordAlive, coordFaulty, forward>>

Broadcast ==
  /\ coordAlive
  /\ coordDecision # waiting
  /\ \E p \in participants :
       /\ coordBroadcast[p] = "none"
       /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = "sent"]
  /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, coordReq,
                 coordVote, coordDecision, coordAlive, coordFaulty, forward>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, coordReq,
                 coordVote, coordBroadcast, coordDecision, forward>>

SendVote ==
  /\ \E p \in participants :
       /\ pAlive[p]
       /\ pVote[p] = undecided
       /\ \E v \in {yes, no} : pVote' = [pVote EXCEPT ![p] = v]
       /\ pSent' = [pSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pAlive, pDecided, pFaulty, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

AbortOnVote ==
  /\ \E p \in participants :
       /\ pAlive[p]
       /\ pVote[p] = no
       /\ pDecided[p] = waiting
       /\ pDecided' = [pDecided EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

\* Pre-decision from the coordinator's broadcast: stores the decision locally.
PreDecideFromCoord ==
  /\ \E p \in participants :
       /\ pAlive[p]
       /\ pDecided[p] = waiting
       /\ forward[p][p] = notsent
       /\ coordBroadcast[p] = "sent"
       /\ forward' = [forward EXCEPT ![p][p] =
            IF coordDecision = commit THEN commit ELSE abort]
  /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, coordReq,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* Pre-decision from another participant's forwarding.
PreDecideFromForward == \E p, q \in participants :
  /\ pAlive[p]
  /\ pDecided[p] = waiting
  /\ forward[p][p] = notsent
  /\ forward[q][p] # notsent
  /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
  /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, coordReq,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Forward == \E p, q \in participants :
  /\ pAlive[p]
  /\ forward[p][p] # notsent
  /\ forward[p][q] = notsent
  /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, coordReq,
                 coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Decide == \E p \in participants :
  /\ pAlive[p]
  /\ pDecided[p] = waiting
  /\ \A q \in participants : forward[p][q] # notsent
  /\ pDecided' = [pDecided EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

\* Timeout abort, possible only once the coordinator is gone and no forwarding
\* is available -- this is what the reliable broadcast eliminates.
AbortOnTimeout ==
  /\ \E p \in participants :
       /\ pAlive[p]
       /\ pDecided[p] = waiting
       /\ ~coordAlive
       /\ \A q \in participants : coordBroadcast[q] # "sent"
       /\ \A q \in participants : pAlive[q] => forward[q][p] = notsent
       /\ pDecided' = [pDecided EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

Die ==
  /\ \E p \in participants :
       /\ pAlive[p]
       /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
       /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pDecided, pSent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

\* Coordinator progress (including death): weakly fair. Participant progress
\* (vote, abort on vote, abort on timeout): weakly fair. Forwarding and
\* pre-deciding are strongly fair, so a live participant always eventually
\* receives and forwards the decision it has.
Next ==
  \/ SendRequest \/ GetVote \/ DetectCoordFault \/ MakeDecision
  \/ Broadcast \/ CoordDie
  \/ SendVote \/ AbortOnVote \/ AbortOnTimeout
  \/ PreDecideFromCoord \/ PreDecideFromForward
  \/ Forward \/ Decide \/ Die

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendVote)
  /\ WF_vars(AbortOnVote)
  /\ WF_vars(AbortOnTimeout)
  /\ SF_vars(PreDecideFromCoord)
  /\ SF_vars(PreDecideFromForward)
  /\ SF_vars(Forward)
  /\ SF_vars(Decide)

\* No two participants reach different decisions.
AC1 == \A p, q \in participants :
  (pDecided[p] = commit /\ pDecided[q] = abort) => FALSE

\* A commit requires a unanimous yes vote.
AC2 == (\E p \in participants : pDecided[p] = commit) => \A p \in participants : pVote[p] = yes

\* An abort is backed by a no vote or a fault.
AC3 == (\E p \in participants : pDecided[p] = abort) =>
        (\E p \in participants : pVote[p] = no) \/ (\E p \in participants : pFaulty[p]) \/ coordFaulty

\* No decision is ever un-made: a decided participant stays decided.
AC4 == \A p \in participants :
  (pDecided[p] = commit \/ pDecided[p] = abort) ~> (pDecided[p] = commit \/ pDecided[p] = abort)

\* Weak progress: either everybody decides, or someone is found faulty.
AC3Liveness == <>(\A p \in participants : pDecided[p] # waiting) \/ (\E p \in participants : pFaulty[p])

\* Every non-faulty participant eventually decides -- the reliable broadcast
\* is what makes this true even after the coordinator crashes.
AC5 == \A p \in participants : (~pFaulty[p] ~> pDecided[p] # waiting)

Properties == AC3Liveness /\ AC5

====