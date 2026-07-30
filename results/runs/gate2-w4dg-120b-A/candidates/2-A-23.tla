---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pState, pAlive, pDecide, pFaulty, pVoted, coordState, coordAlive, coordFaulty
VARIABLES fwd

vars == <<pState, pAlive, pDecide, pFaulty, pVoted,
          coordState, coordAlive, coordFaulty, fwd>>

TypeOK ==
    /\ pState \in [participants -> {undecided, commit, abort}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecide \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVoted \in [participants -> {yes, no, undecided}]
    /\ coordState \in {waiting, yes, no}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
    /\ pState = [pa \in participants |-> undecided]
    /\ pAlive = [pa \in participants |-> TRUE]
    /\ pDecide = [pa \in participants |-> undecided]
    /\ pFaulty = [pa \in participants |-> FALSE]
    /\ pVoted = [pa \in participants |-> undecided]
    /\ coordState = waiting
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ fwd = [pa \in participants |-> [pb \in participants |-> notsent]]

\* Coordinator actions are inherited from ACP-SB; they are listed here
\* unchanged, so the NB protocol keeps exactly the same coordinator logic.
SendRequest ==
    /\ coordAlive
    /\ coordState = waiting
    /\ coordState' = yes
    /\ UNCHANGED <<pState, pAlive, pDecide, pFaulty, pVoted,
                   coordAlive, coordFaulty, fwd>>

GetVote ==
    /\ coordAlive
    /\ coordState = yes
    /\ \E pa \in participants :
         /\ pAlive[pa]
         /\ pVoted[pa] = undecided
         /\ pVoted' = [pVoted EXCEPT ![pa] = yes]
    /\ UNCHANGED <<pState, pAlive, pDecide, pFaulty,
                   coordState, coordAlive, coordFaulty, fwd>>

DetectFault ==
    /\ coordAlive
    /\ coordState = yes
    /\ \E pa \in participants :
         /\ pAlive[pa]
         /\ pVoted[pa] = undecided
         /\ pVoted' = [pVoted EXCEPT ![pa] = no]
    /\ UNCHANGED <<pState, pAlive, pDecide, pFaulty,
                   coordState, coordAlive, coordFaulty, fwd>>

MakeDecision ==
    /\ coordAlive
    /\ coordState \in {yes, no}
    /\ coordState' = no
    /\ UNCHANGED <<pState, pAlive, pDecide, pFaulty, pVoted,
                   coordAlive, coordFaulty, fwd>>

\* A broadcast delivers the decision to every participant directly.
Broadcast ==
    /\ coordAlive
    /\ coordState = no
    /\ \E pa \in participants :
         /\ fwd[pa][pa] = notsent
         /\ fwd' = [fwd EXCEPT ![pa][pa] = IF coordState = yes THEN commit ELSE abort]
    /\ UNCHANGED <<pState, pAlive, pDecide, pFaulty,
                   pVoted, coordState, coordAlive, coordFaulty>>

\* Participants forward decisions they have received to every other participant,
\* so a decision can survive a coordinator crash and still reach all nodes.
PreDecideFromCoord ==
    /\ \E pa \in participants :
         /\ pAlive[pa]
         /\ pState[pa] = undecided
         /\ fwd[pa][pa] # notsent
         /\ pState' = [pState EXCEPT ![pa] = fwd[pa][pa]]
    /\ UNCHANGED <<pAlive, pDecide, pFaulty, pVoted,
                   coordState, coordAlive, coordFaulty, fwd>>

PreDecideFromPeer ==
    /\ \E pa \in participants :
         /\ pAlive[pa]
         /\ pState[pa] = undecided
         /\ \E pb \in participants :
              /\ pb # pa
              /\ fwd[pb][pa] # notsent
              /\ pState' = [pState EXCEPT ![pa] = fwd[pb][pa]]
    /\ UNCHANGED <<pAlive, pDecide, pFaulty, pVoted,
                   coordState, coordAlive, coordFaulty, fwd>>

Forward ==
    /\ \E pa \in participants :
         /\ pAlive[pa]
         /\ pState[pa] # undecided
         /\ \E pb \in participants :
              /\ pb # pa
              /\ fwd[pa][pb] = notsent
              /\ fwd' = [fwd EXCEPT ![pa][pb] = pState[pa]]
    /\ UNCHANGED <<pState, pAlive, pDecide, pFaulty,
                   pVoted, coordState, coordAlive, coordFaulty>>

\* A participant decides locally only once every other participant has been
\* forwarded the pre-decision it is about to adopt.
Decide ==
    /\ \E pa \in participants :
         /\ pAlive[pa]
         /\ pState[pa] # undecided
         /\ \A pb \in participants : pb # pa => fwd[pa][pb] # notsent
         /\ pState' = [pState EXCEPT ![pa] = pDecide[pa]]
    /\ UNCHANGED <<pAlive, pDecide, pFaulty, pVoted,
                   coordState, coordAlive, coordFaulty, fwd>>

AbortOnTimeout ==
    /\ \E pa \in participants :
         /\ pAlive[pa]
         /\ pState[pa] = undecided
         /\ ~coordAlive
         /\ \A pb \in participants : fwd[coordState][pb] = notsent
         /\ \A pb \in participants : pFaulty[pb] => FALSE
         /\ pState' = [pState EXCEPT ![pa] = abort]
    /\ UNCHANGED <<pAlive, pDecide, pFaulty, pVoted,
                   coordState, coordAlive, coordFaulty, fwd>>

Die ==
    /\ \E pa \in participants :
         /\ pAlive[pa]
         /\ pAlive' = [pAlive EXCEPT ![pa] = FALSE]
         /\ pFaulty' = [pFaulty EXCEPT ![pa] = TRUE]
    /\ UNCHANGED <<pState, pDecide, pVoted,
                   coordState, coordAlive, coordFaulty, fwd>>

Next ==
    \/ SendRequest \/ GetVote \/ DetectFault \/ MakeDecision \/ Broadcast
    \/ PreDecideFromCoord \/ PreDecideFromPeer
    \/ Forward \/ Decide \/ AbortOnTimeout \/ Die

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(PreDecideFromCoord)
    /\ WF_vars(PreDecideFromPeer)
    /\ WF_vars(Forward)
    /\ WF_vars(Decide)
    /\ WF_vars(AbortOnTimeout)

\* Safety: no two participants can ever end up in different final states.
AC1 ==
    \A pa, pb \in participants :
        (pState[pa] = commit) => (pState[pb] # abort)

\* Safety: commit only when everyone voted yes.
AC2 ==
    \A pa \in participants :
        (pState[pa] = commit) => (\A pb \in participants : pVoted[pb] = yes)

\* Safety: abort only if a no vote or a failure was observed.
AC3 ==
    \A pa \in participants :
        (pState[pa] = abort) =>
            \/ (\E pb \in participants : pVoted[pb] = no)
            \/ (\E pb \in participants : pFaulty[pb])
            \/ coordFaulty

\* Safety: irrevocability of the final decision.
AC4 ==
    \A pa \in participants :
        (pState[pa] # undecided) => (pState[pa] = pDecide[pa])

\* Liveness: the protocol always resolves or exposes a failure.
AC3Liveness ==
    <>(\A pa \in participants : pState[pa] # undecided) \/ coordFaulty

\* Liveness: every non-faulty participant eventually decides.
AC5 ==
    \A pa \in participants : (pAlive[pa] /\ ~pFaulty[pa]) ~> (pState[pa] # undecided)

TypeInvNB == TypeOK
Properties == AC3Liveness /\ AC5
====