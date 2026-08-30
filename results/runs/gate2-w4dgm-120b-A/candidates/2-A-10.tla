---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding table entry: a pre-decision a participant has received (or not)
\* and an as-yet-unforwarded destination participant (or notsent).
Entry == [msg: {notsent, commit, abort}, dst: participants \cup {notsent}]

VARIABLES pVote, pAlive, decision, pFaulty, pVoted, pReq, pV, pB, pD, cAlive, cFaulty, pFwd

vars == <<pVote, pAlive, decision, pFaulty, pVoted, pReq, pV, pB, pD, cAlive, cFaulty, pFwd>>

TypeInvNB ==
  /\ pVote \in [participants -> {yes, no, undecided}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ decision \in {notsent, commit, abort}
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pVoted \in [participants -> BOOLEAN]
  /\ pReq \in {notsent, waiting}
  /\ pV \in {notsent, yes, no}
  /\ pB \in [participants -> {notsent, waiting}]
  /\ pD \in [participants -> {notsent, commit, abort}]
  /\ cAlive \in BOOLEAN
  /\ cFaulty \in BOOLEAN
  /\ pFwd \in [participants -> [participants -> Entry]]

Init ==
  /\ pVote = [p \in participants |-> undecided]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ decision = notsent
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ pVoted = [p \in participants |-> FALSE]
  /\ pReq = notsent
  /\ pV = notsent
  /\ pB = [p \in participants |-> notsent]
  /\ pD = [p \in participants |-> notsent]
  /\ cAlive = TRUE
  /\ cFaulty = FALSE
  /\ pFwd = [p \in participants |-> [q \in participants |-> [msg |-> notsent, dst |-> notsent]]]

\* Coordinator actions (base ACP-SB protocol, carried over unchanged):
SendReq ==
  /\ cAlive
  /\ decision = notsent
  /\ pReq = notsent
  /\ pReq' = waiting
  /\ UNCHANGED <<pVote, pAlive, decision, pFaulty, pVoted, pV, pB, pD, cAlive, cFaulty, pFwd>>

\* The coordinator accepts at most one vote from each participant.
GetVote(p) ==
  /\ cAlive
  /\ pReq = waiting
  /\ pAlive[p]
  /\ pVoted[p] = FALSE
  /\ pV # notsent
  /\ pVote' = [pVote EXCEPT ![p] = pV]
  /\ pVoted' = [pVoted EXCEPT ![p] = TRUE]
  /\ pV' = notsent
  /\ UNCHANGED <<pAlive, decision, pFaulty, pReq, pB, pD, cAlive, cFaulty, pFwd>>

FaultDetect(p) ==
  /\ pAlive[p]
  /\ pVoted[p] = FALSE
  /\ pV # notsent
  /\ pVoted' = [pVoted EXCEPT ![p] = TRUE]
  /\ pVote' = [pVote EXCEPT ![p] = pV]
  /\ pV' = notsent
  /\ UNCHANGED <<pAlive, decision, pFaulty, pReq, pB, pD, cAlive, cFaulty, pFwd>>

MakeDecision ==
  /\ decision = notsent
  /\ \A p \in participants : pAlive[p] => pVoted[p]
  /\ decision' = IF \A p \in participants : pAlive[p] => pVote[p] = yes
                 THEN commit ELSE abort
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pVoted, pReq, pV, pB, pD, cAlive, cFaulty, pFwd>>

Broadcast(p) ==
  /\ decision # notsent
  /\ cAlive
  /\ pAlive[p]
  /\ pB[p] = notsent
  /\ pB' = [pB EXCEPT ![p] = waiting]
  /\ UNCHANGED <<pVote, pAlive, decision, pFaulty, pVoted, pReq, pV, pD, cAlive, cFaulty, pFwd>>

DieCoordinator ==
  /\ cAlive
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, decision, pFaulty, pVoted, pReq, pV, pB, pD, pFwd>>

\* Participant actions, adding reliable broadcast with forwarding:
SendVote(p) ==
  /\ pAlive[p]
  /\ pV = notsent
  /\ \E x \in {yes, no} : pV' = x
  /\ UNCHANGED <<pVote, pAlive, decision, pFaulty, pVoted, pReq, pB, pD, cAlive, cFaulty, pFwd>>

\* A participant may locally abort before the coordinator decides.
AbortOnVote(p) ==
  /\ pAlive[p]
  /\ pVote[p] = no
  /\ pD[p] = notsent
  /\ pD' = [pD EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, decision, pFaulty, pVoted, pReq, pV, pB, cAlive, cFaulty, pFwd>>

AbortTimeout(p) ==
  /\ pAlive[p]
  /\ pD[p] = notsent
  /\ ~cAlive
  /\ \A q \in participants : ~pAlive[q] => pB[q] = notsent
  /\ \A q \in participants : pAlive[q] => pFwd[q][p].dst # notsent
  /\ pD' = [pD EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, decision, pFaulty, pVoted, pReq, pV, pB, cAlive, cFaulty, pFwd>>

\* Pre-decision from the coordinator's broadcast (already forwarded to this p).
PreDecideFromCoord(p) ==
  /\ pAlive[p]
  /\ pFwd[p][p].msg = notsent
  /\ pB[p] = waiting
  /\ pFwd[p][p]' = [msg |-> decision, dst |-> p]
  /\ UNCHANGED <<pVote, pAlive, decision, pFaulty, pVoted, pReq, pV, pB, pD, cAlive, cFaulty, pFwd>>

\* Pre-decision from another participant's forwarding.
PreDecideFromFwd(p, q) ==
  /\ pAlive[p]
  /\ pFwd[p][p].msg = notsent
  /\ pFwd[q][p].msg # notsent
  /\ pFwd[p][p]' = [msg |-> pFwd[q][p].msg, dst |-> p]
  /\ UNCHANGED <<pVote, pAlive, decision, pFaulty, pVoted, pReq, pV, pB, pD, cAlive, cFaulty, pFwd>>

Forward(p, q) ==
  /\ pAlive[p]
  /\ pFwd[p][p].msg # notsent
  /\ pFwd[p][q].msg = notsent
  /\ pFwd[p][q]' = [msg |-> pFwd[p][p].msg, dst |-> q]
  /\ UNCHANGED <<pVote, pAlive, decision, pFaulty, pVoted, pReq, pV, pB, pD, cAlive, cFaulty, pFwd>>

Decide(p) ==
  /\ pAlive[p]
  /\ pD[p] = notsent
  /\ \A q \in participants : q # p => pFwd[p][q].msg # notsent
  /\ pD' = [pD EXCEPT ![p] = pFwd[p][p].msg]
  /\ UNCHANGED <<pVote, pAlive, decision, pFaulty, pVoted, pReq, pV, pB, cAlive, cFaulty, pFwd>>

DieParticipant(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, decision, pVoted, pReq, pV, pB, pD, cAlive, cFaulty, pFwd>>

Next ==
  \/ SendReq \/ MakeDecision \/ DieCoordinator
  \/ \E p \in participants :
       \/ GetVote(p) \/ FaultDetect(p) \/ Broadcast(p)
       \/ SendVote(p) \/ AbortOnVote(p) \/ AbortTimeout(p)
       \/ PreDecideFromCoord(p) \/ Decide(p) \/ DieParticipant(p)
       \/ \E q \in participants : PreDecideFromFwd(p, q) \/ Forward(p, q)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ TRUE
  /\ WF_vars(DieCoordinator)
  /\ WF_vars(\E p \in participants : GetVote(p))
  /\ WF_vars(\E p \in participants : FaultDetect(p))
  /\ WF_vars(\E p \in participants : Broadcast(p))
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortOnVote(p))
  /\ WF_vars(\E p \in participants : AbortTimeout(p))
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants : \E q \in participants : PreDecideFromFwd(p, q))
  /\ WF_vars(\E p \in participants : \E q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : DieParticipant(p))

\* Stronger than Agreement: no two participants can reach different decisions.
NoConflictingDecision ==
  \A p, q \in participants : (pD[p] # notsent /\ pD[q] # notsent) => (pD[p] = pD[q])

ValidCommit ==
  \A p \in participants : pD[p] = commit => \A q \in participants : pVote[q] = yes

ValidAbort ==
  \A p \in participants :
    pD[p] = abort =>
      \/ (\E q \in participants : pVote[q] = no)
      \/ (\E q \in participants : pFaulty[q])
      \/ cFaulty

Irreversible == \A p \in participants : (pD[p] # notsent) ~> (pD[p] = pD[p])

DecidePromptly == \A p \in participants : pAlive[p] ~> (pD[p] # notsent)

====