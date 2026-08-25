---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Sets and derived constants
\* ----------------------------------------------------------------------
Participants == participants
Vote        == {yes, no}
DecisionVal == {commit, abort, undecided}
ForwardStatus == {commit, abort, notsent}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    cAlive,          \* coordinator is alive?
    cFaulty,         \* coordinator is faulty?
    cDecision,       \* coordinator's decision (commit/abort/undecided)
    cSent,           \* for each participant whether coordinator has broadcast to it
    pAlive,          \* participant i is alive?
    pFaulty,         \* participant i is faulty?
    pVote,           \* participant i's vote (yes/no)
    pVoteSent,       \* participant i has sent its vote
    pPreDec,         \* participant i's pre‑decision (forwarding table entry for itself)
    pForwarded,      \* for each i,j whether i has forwarded its pre‑decision to j
    pDecision        \* participant i's final decision (commit/abort/undecided)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ cAlive   = TRUE
    /\ cFaulty  = FALSE
    /\ cDecision = undecided
    /\ cSent    = [i \in Participants |-> FALSE]
    /\ pAlive   = [i \in Participants |-> TRUE]
    /\ pFaulty  = [i \in Participants |-> FALSE]
    /\ pVote    \in [Participants -> Vote]
    /\ pVoteSent = [i \in Participants |-> FALSE]
    /\ pPreDec  = [i \in Participants |-> notsent]
    /\ pForwarded = [i \in Participants |-> [j \in Participants |-> FALSE]]
    /\ pDecision = [i \in Participants |-> undecided]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendVote(i) ==
    /\ i \in Participants
    /\ pAlive[i]
    /\ ~pVoteSent[i]
    /\ pVoteSent' = [pVoteSent EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cSent,
                    pAlive, pFaulty, pVote,
                    pPreDec, pForwarded, pDecision>>

CollectVotes ==
    /\ \A i \in Participants : pAlive[i] => pVoteSent[i]
    /\ cDecision' = IF \A i \in Participants : pAlive[i] => pVote[i] = yes
                    THEN commit ELSE abort
    /\ UNCHANGED <<cAlive, cFaulty, cSent,
                    pAlive, pFaulty, pVote, pVoteSent,
                    pPreDec, pForwarded, pDecision>>

CoordinatorBroadcast(i) ==
    /\ i \in Participants
    /\ cAlive
    /\ cDecision # undecided
    /\ ~cSent[i]
    /\ cSent' = [cSent EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision,
                    pAlive, pFaulty, pVote, pVoteSent,
                    pPreDec, pForwarded, pDecision>>

CoordinatorDie ==
    /\ cAlive
    /\ cAlive'  = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<cDecision, cSent,
                    pAlive, pFaulty, pVote, pVoteSent,
                    pPreDec, pForwarded, pDecision>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantPreDecFromCoord(i) ==
    /\ i \in Participants
    /\ pAlive[i]
    /\ pPreDec[i] = notsent
    /\ cSent[i]
    /\ pPreDec' = [pPreDec EXCEPT ![i] = IF cDecision = commit THEN commit ELSE abort]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cSent,
                    pAlive, pFaulty, pVote, pVoteSent,
                    pForwarded, pDecision>>

ParticipantPreDecFromForward(i) ==
    /\ i \in Participants
    /\ pAlive[i]
    /\ pPreDec[i] = notsent
    /\ \E j \in Participants :
          /\ pForwarded[j][i]
          /\ pPreDec[j] # notsent
    /\ LET dec == IF \E j \in Participants :
                     pForwarded[j][i] /\ pPreDec[j] = commit
                 THEN commit ELSE abort
       IN pPreDec' = [pPreDec EXCEPT ![i] = dec]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cSent,
                    pAlive, pFaulty, pVote, pVoteSent,
                    pForwarded, pDecision>>

ParticipantForward(i, j) ==
    /\ i \in Participants
    /\ j \in Participants
    /\ pAlive[i]
    /\ pPreDec[i] # notsent
    /\ ~pForwarded[i][j]
    /\ pForwarded' = [pForwarded EXCEPT ![i][j] = TRUE]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cSent,
                    pAlive, pFaulty, pVote, pVoteSent,
                    pPreDec, pDecision>>

ParticipantDecide(i) ==
    /\ i \in Participants
    /\ pAlive[i]
    /\ pPreDec[i] # notsent
    /\ \A j \in Participants : pForwarded[i][j]
    /\ pDecision' = [pDecision EXCEPT ![i] = IF pPreDec[i] = commit THEN commit ELSE abort]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cSent,
                    pAlive, pFaulty, pVote, pVoteSent,
                    pPreDec, pForwarded>>

AbortOnTimeout(i) ==
    /\ i \in Participants
    /\ pAlive[i]
    /\ pDecision[i] = undecided
    /\ ~cAlive
    /\ \A k \in Participants : pPreDec[k] = notsent
    /\ \A d \in Participants :
          ~pAlive[d] => \A a \in Participants :
                         pAlive[a] => ~pForwarded[d][a]
    /\ pDecision' = [pDecision EXCEPT ![i] = abort]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cSent,
                    pAlive, pFaulty, pVote, pVoteSent,
                    pPreDec, pForwarded>>

ParticipantDie(i) ==
    /\ i \in Participants
    /\ pAlive[i]
    /\ pAlive'   = [pAlive EXCEPT ![i] = FALSE]
    /\ pFaulty'  = [pFaulty EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cSent,
                    pVote, pVoteSent,
                    pPreDec, pForwarded, pDecision>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in Participants : SendVote(i)
    \/ CollectVotes
    \/ \E i \in Participants : CoordinatorBroadcast(i)
    \/ CoordinatorDie
    \/ \E i \in Participants : ParticipantPreDecFromCoord(i)
    \/ \E i \in Participants : ParticipantPreDecFromForward(i)
    \/ \E i \in Participants : \E j \in Participants : ParticipantForward(i, j)
    \/ \E i \in Participants : ParticipantDecide(i)
    \/ \E i \in Participants : AbortOnTimeout(i)
    \/ \E i \in Participants : ParticipantDie(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB ==
    Init /\ [] [Next]_<<cAlive, cFaulty, cDecision, cSent,
                 pAlive, pFaulty, pVote, pVoteSent,
                 pPreDec, pForwarded, pDecision>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ cAlive   \in BOOLEAN
    /\ cFaulty  \in BOOLEAN
    /\ cDecision \in DecisionVal
    /\ cSent    \in [Participants -> BOOLEAN]
    /\ pAlive   \in [Participants -> BOOLEAN]
    /\ pFaulty  \in [Participants -> BOOLEAN]
    /\ pVote    \in [Participants -> Vote]
    /\ pVoteSent \in [Participants -> BOOLEAN]
    /\ pPreDec  \in [Participants -> ForwardStatus]
    /\ pForwarded \in [Participants -> [Participants -> BOOLEAN]]
    /\ pDecision \in [Participants -> DecisionVal]

====