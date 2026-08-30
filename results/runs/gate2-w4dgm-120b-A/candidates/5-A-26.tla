---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, coordReq, coordVote,
          coordSent, coordDecision, coordAlive, coordFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent, coordReq, coordVote,
           coordSent, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecision \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pSent \in [participants -> BOOLEAN]
  /\ coordReq \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {notSent, waiting}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pDecision = [p \in participants |-> undecided]
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ pSent = [p \in participants |-> FALSE]
  /\ coordReq = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notSent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendReq(p) ==
  /\ coordAlive
  /\ ~coordReq[p]
  /\ coordReq' = [coordReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordVote,
                 coordSent, coordDecision, coordAlive, coordFaulty>>

RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReq[p]
  /\ coordVote[p] = waiting
  /\ pSent[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = pVote[p]]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordReq,
                 coordSent, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordReq[p]
  /\ coordVote[p] = waiting
  /\ ~pAlive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordReq,
                 coordVote, coordSent, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordReq,
                 coordVote, coordSent, coordAlive, coordFaulty>>

CoordBroadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notSent
  /\ coordSent' = [coordSent EXCEPT ![p] = waiting]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordReq,
                 coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, coordReq,
                 coordVote, coordSent, coordDecision, coordFaulty>>

PsendVote(p) ==
  /\ pAlive[p]
  /\ coordReq[p]
  /\ ~pSent[p]
  /\ pSent' = [pSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty,
                 coordReq, coordVote, coordSent, coordDecision,
                 coordAlive, coordFaulty>>

PabortOnVote(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ pSent[p]
  /\ pVote[p] = no
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq,
                 coordVote, coordSent, coordDecision,
                 coordAlive, coordFaulty>>

PabortOnTimeout(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ ~coordAlive
  /\ ~coordReq[p]
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq,
                 coordVote, coordSent, coordDecision,
                 coordAlive, coordFaulty>>

Pdecide(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ coordSent[p] = waiting
  /\ pDecision' = [pDecision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq,
                 coordVote, coordSent, coordDecision,
                 coordAlive, coordFaulty>>

Pdie(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pDecision, pSent, coordReq,
                 coordVote, coordSent, coordDecision,
                 coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : SendReq(p)
  \/ \E p \in participants : RecvVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants : CoordBroadcast(p)
  \/ CoordDie
  \/ \E p \in participants : PsendVote(p)
  \/ \E p \in participants : PabortOnVote(p)
  \/ \E p \in participants : PabortOnTimeout(p)
  \/ \E p \in participants : Pdecide(p)
  \/ \E p \in participants : Pdie(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants :
       WF_vars(PsendVote(p))
       /\ WF_vars(PabortOnVote(p))
       /\ WF_vars(PabortOnTimeout(p))
       /\ WF_vars(Pdecide(p))

NoTwoDecideDifferently ==
  \A p, q \in participants :
    (pDecision[p] = commit /\ pDecision[q] = abort) => FALSE

CommitValidity ==
  \E p \in participants : pDecision[p] = commit => (\A q \in participants : pVote[q] = yes)

AbortValidity ==
  \E p \in participants :
    pDecision[p] = abort =>
      \/ (\E q \in participants : pVote[q] = no)
      \/ (\E q \in participants : ~pAlive[q])
      \/ ~coordAlive

IrreversibleDecision ==
  \A p \in participants :
    /\ (pDecision[p] = commit) ~> (pDecision[p] = commit)
    /\ (pDecision[p] = abort) ~> (pDecision[p] = abort)

EventuallyDecideOrCrash ==
  <>(\A p \in participants : pDecision[p] # undecided \/ coordFaulty \/ (\E q \in participants : pFaulty[q]))

====