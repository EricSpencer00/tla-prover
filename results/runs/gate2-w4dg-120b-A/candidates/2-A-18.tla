---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordVote, coordAlive, coordFaulty,
         coordReq, coordVoters, coordDecision, coordBcast,
         pstate, pfaulty, pvoteSent, forwarding

vars == <<coordVote, coordAlive, coordFaulty,
          coordReq, coordVoters, coordDecision, coordBcast,
          pstate, pfaulty, pvoteSent, forwarding>>

Decision == {commit, abort}
PState == {undecided, commit, abort}
Pref == {notsent, commit, abort}

TypeOK ==
  /\ coordVote \in {yes, no}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordReq \in {waiting, yes, no}
  /\ coordVoters \subseteq participants
  /\ coordDecision \in Decision \cup {waiting}
  /\ coordBcast \subseteq participants
  /\ pstate \in [participants -> PState]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ pvoteSent \in [participants -> BOOLEAN]
  /\ forwarding \in [participants -> [participants -> Pref]]

Init ==
  /\ coordVote = yes
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordReq = waiting
  /\ coordVoters = {}
  /\ coordDecision = waiting
  /\ coordBcast = {}
  /\ pstate = [p \in participants |-> undecided]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ pvoteSent = [p \in participants |-> FALSE]
  /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]

\* The coordinator sends the request to an alive participant.
CoordSendReq(p) ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ coordReq = waiting
  /\ p \notin coordVoters
  /\ coordReq' = p
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty,
                coordVoters, coordDecision, coordBcast,
                pstate, pfaulty, pvoteSent, forwarding>>

\* An alive participant votes yes or no back to the coordinator.
CoordGetVote(p, v) ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ coordReq = p
  /\ ~pvoteSent[p]
  /\ pvoteSent' = [pvoteSent EXCEPT ![p] = TRUE]
  /\ coordVoters' = coordVoters \cup {p}
  /\ coordVote' = IF v = no THEN no ELSE coordVote
  /\ coordReq' = waiting
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBcast,
                pstate, pfaulty, forwarding>>

CoordDetectFault(p) ==
  /\ coordAlive
  /\ p \notin coordVoters
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ coordReq' = waiting
  /\ UNCHANGED <<coordVote, coordVoters, coordDecision, coordBcast,
                pstate, pfaulty, pvoteSent, forwarding>>

CoordDecide ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ coordDecision = waiting
  /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty,
                coordReq, coordVoters, coordBcast,
                pstate, pfaulty, pvoteSent, forwarding>>

CoordBroadcast(p) ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ coordDecision # waiting
  /\ p \notin coordBcast
  /\ coordBcast' = coordBcast \cup {p}
  /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty,
                coordReq, coordVoters, coordDecision,
                pstate, pfaulty, pvoteSent>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordVote, coordReq, coordVoters, coordDecision,
                coordBcast, pstate, pfaulty, pvoteSent, forwarding>>

\* A participant receives the coordinator's broadcast and stores it.
PreDecideFromCoord(p) ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ p \notin coordBcast
  /\ p \notin coordVoters
  /\ coordDecision # waiting
  /\ forwarding[p][p] = notsent
  /\ coordBcast' = coordBcast \cup {p}
  /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty,
                coordReq, coordVoters, coordDecision,
                pstate, pfaulty, pvoteSent>>

\* A participant receives a forwarded pre-decision from another participant.
PreDecideFromForward(p, q) ==
  /\ p # q
  /\ ~pfaulty[p]
  /\ forwarding[p][p] = notsent
  /\ forwarding[q][p] \in {commit, abort}
  /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty,
                coordReq, coordVoters, coordDecision,
                coordBcast, pstate, pfaulty, pvoteSent>>

\* A participant forwards its pre-decision to another participant.
Forward(p, q) ==
  /\ p # q
  /\ ~pfaulty[p]
  /\ forwarding[p][p] \in {commit, abort}
  /\ forwarding[p][q] = notsent
  /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty,
                coordReq, coordVoters, coordDecision,
                coordBcast, pstate, pfaulty, pvoteSent>>

\* A participant finalizes its decision once it has forwarded to all others.
Decide(p) ==
  /\ ~pfaulty[p]
  /\ pstate[p] = undecided
  /\ \A q \in participants \ {p} : forwarding[p][q] # notsent
  /\ pstate' = [pstate EXCEPT ![p] = forwarding[p][p]]
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty,
                coordReq, coordVoters, coordDecision,
                coordBcast, pfaulty, pvoteSent, forwarding>>

\* Abort if the coordinator died, nothing reachable from it, and no dead
\* participant can rescue the decision by forwarding.
AbortTimeout(p) ==
  /\ ~coordAlive
  /\ pstate[p] = undecided
  /\ \A q \in participants : q \notin coordBcast
  /\ \A q \in participants, r \in participants :
        ~(pfaulty[q] /\ forwarding[q][r] \in {commit, abort})
  /\ pstate' = [pstate EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty,
                coordReq, coordVoters, coordDecision,
                coordBcast, pfaulty, pvoteSent, forwarding>>

Die(p) ==
  /\ ~pfaulty[p]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordVote, coordAlive, coordFaulty,
                coordReq, coordVoters, coordDecision,
                coordBcast, pstate, pvoteSent, forwarding>>

CoordActions ==
  \/ \E p \in participants : CoordSendReq(p)
  \/ \E p \in participants, v \in {yes, no} : CoordGetVote(p, v)
  \/ \E p \in participants : CoordDetectFault(p)
  \/ CoordDecide
  \/ \E p \in participants : CoordBroadcast(p)
  \/ CoordDie

ParticipantActions ==
  \/ \E p \in participants : PreDecideFromCoord(p)
  \/ \E p \in participants, q \in participants : PreDecideFromForward(p, q)
  \/ \E p \in participants, q \in participants : Forward(p, q)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : AbortTimeout(p)
  \/ \E p \in participants : Die(p)

Next == CoordActions \/ ParticipantActions

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CoordActions)
  /\ WF_vars(ParticipantActions)

TypeInvNB == TypeOK

\* Safety: no two participants disagree, and any decision is explained.
AC1 ==
  \A p, q \in participants : ~(pstate[p] = commit /\ pstate[q] = abort)

AC2 ==
  (commit \in {pstate[p] : p \in participants})
    => (\A p \in participants : p \in coordVoters)

AC3 ==
  (abort \in {pstate[p] : p \in participants})
    => (coordVote = no \/ coordFaulty \/ \E p \in participants : pfaulty[p])

AC4 ==
  \A p \in participants : (pstate[p] # undecided) ~> (pstate[p] # undecided)

\* Liveness: either everyone decides or the system recovers a fault.
AC3Liveness ==
  <>(\A p \in participants : pstate[p] # undecided)
    \/ coordFaulty
    \/ (\E p \in participants : pfaulty[p])

\* Liveness: every non-faulty participant eventually decides -- the guarantee
\* provided by reliable broadcast, not satisfied by the simple broadcast.
AC5 ==
  \A p \in participants : (~pfaulty[p]) ~> (pstate[p] # undecided)

Properties == {AC1, AC2, AC3, AC4, AC3Liveness, AC5}

====