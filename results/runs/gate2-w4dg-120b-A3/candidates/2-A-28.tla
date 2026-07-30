---- MODULE ACP_NB ----
EXTENDS Naturals

\* Non-Blocking Atomic Commitment Protocol (ACP-NB) extending the broadcast
\* variant ACP-SB with reliable broadcast. Each participant forwards its
\* pre-decision to all others before finalizing; this guarantees that a
\* non-faulty participant eventually decides even if the coordinator crashes.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voteSent, coordReq, coordVote,
          coordBroadcast, coordDecision, coordAlive, coordFaulty

vars == <<pstate, alive, decision, faulty, voteSent, coordReq, coordVote,
          coordBroadcast, coordDecision, coordAlive, coordFaulty>>

TypeInvNB ==
  /\ pstate \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {waiting, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordReq \in {yes, no, undecided}
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in [participants -> {notSent, commit, abort}]
  /\ coordDecision \in {waiting, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordReq = undecided
  /\ coordVote = undecided
  /\ coordBroadcast = [p \in participants |-> notSent]
  /\ coordDecision = waiting
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator actions: the same as in ACP-SB, so reused verbatim.
SendRequest ==
  /\ coordAlive
  /\ coordReq = undecided
  /\ \E v \in {yes, no} : coordReq' = v
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty>>

CoordVote ==
  /\ coordAlive
  /\ coordReq # undecided
  /\ coordVote = undecided
  /\ coordVote' = coordReq
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordReq,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty>>

CoordDetectFault ==
  /\ coordAlive
  /\ coordVote # undecided
  /\ \E p \in participants : pstate[p] = yes \/ pstate[p] = no
  /\ coordDecision' = abort
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordReq,
                 coordVote, coordBroadcast, coordAlive, coordFaulty>>

CoordDecide ==
  /\ coordAlive
  /\ coordVote # undecided
  /\ coordDecision = waiting
  /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordReq,
                 coordVote, coordBroadcast, coordAlive, coordFaulty>>

CoordBroadcast ==
  /\ coordAlive
  /\ coordDecision \in {commit, abort}
  /\ \E p \in participants :
       /\ coordBroadcast[p] = notSent
       /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordReq,
                 coordVote, coordDecision, coordAlive, coordFaulty>>

CoordCrash ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordReq,
                 coordVote, coordBroadcast, coordDecision, coordFaulty>>

\* Participant sends its vote to the coordinator; always available.
SendVote(p) ==
  /\ alive[p]
  /\ ~voteSent[p]
  /\ \E v \in {yes, no} :
       /\ pstate' = [pstate EXCEPT ![p] = v]
       /\ coordReq' = v
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, coordVote, coordBroadcast,
                 coordDecision, coordAlive, coordFaulty>>

AbortParticipant(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ pstate[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty>>

AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ ~coordAlive
  /\ \A q \in participants : coordBroadcast[q] = notSent \/ ~alive[q]
  /\ \A q \in participants : \A r \in participants :
       coordBroadcast[q] # notsent => (r = p \/ ~alive[r])
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A live participant pre-decides on a broadcast decision from the coordinator.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ coordBroadcast[p] \in {commit, abort}
  /\ decision' = [decision EXCEPT ![p] = coordBroadcast[p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A live participant pre-decides on a forwarded decision from another participant.
PreDecideFromPeer(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ \E q \in participants :
       /\ q # p
       /\ coordBroadcast[q] \in {commit, abort}
       /\ decision[p] = waiting
       /\ decision' = [decision EXCEPT ![p] = coordBroadcast[q]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A live participant forwards its pre-decision to a specific other participant.
Forward(p, r) ==
  /\ alive[p]
  /\ decision[p] \in {commit, abort}
  /\ coordBroadcast[r] = notsent
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![r] = decision[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordReq,
                 coordVote, coordDecision, coordAlive, coordFaulty>>

\* A participant finalizes (decides) once it has forwarded to all others.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] \in {commit, abort}
  /\ \A r \in participants : r # p => coordBroadcast[r] # notsent
  /\ decision' = [decision EXCEPT ![p] = decision[p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, decision, voteSent, coordReq, coordVote,
                 coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ SendRequest \/ CoordVote \/ CoordDetectFault \/ CoordDecide
  \/ CoordBroadcast \/ CoordCrash
  \/ \E p \in participants :
       SendVote(p) \/ AbortParticipant(p) \/ AbortTimeout(p)
       \/ PreDecideFromCoord(p) \/ PreDecideFromPeer(p) \/ Decide(p)
       \/ \E r \in participants : Forward(p, r) \/ Die(p)

\* Weak fairness on all progress actions except crashes (which are uncontrolled).
SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendVote(ANY))
  /\ WF_vars(AbortParticipant(ANY))
  /\ WF_vars(PreDecideFromCoord(ANY))
  /\ WF_vars(PreDecideFromPeer(ANY))
  /\ WF_vars(\E r \in participants : Forward(ANY, r))
  /\ WF_vars(Decide(ANY))

\* AC1: no two participants end up in conflicting decisions.
Agree ==
  ~(\E p1, p2 \in participants :
        /\ decision[p1] = commit
        /\ decision[p2] = abort)

\* AC2: a commit implies a unanimous yes vote.
CommitImpliesUnanimous ==
  ~(\E p1, p2 \in participants :
        /\ decision[p1] = commit
        /\ pstate[p2] = no)

\* AC3: an abort is justified by a no vote or a fault.
AbortJustified ==
  ~(\E p1, p2 \in participants :
        /\ decision[p1] = abort
        /\ pstate[p2] = yes
        /\ ~faulty[p2]
        /\ ~coordFaulty)

\* AC4: a decided participant never silently reverts.
Irreversible ==
  \A p \in participants :
    (decision[p] = commit \/ decision[p] = abort) ~> decision[p]

\* AC3(liveness): the protocol eventually resolves or discovers a fault.
Resolves ==
  <>(\A p \in participants : decision[p] \in {commit, abort})
     \/ (\E p \in participants : faulty[p])
     \/ coordFaulty

\* AC5: every non-faulty participant eventually reaches a decision.
EveryoneDecides ==
  \A p \in participants : (alive[p] /\ decision[p] = waiting) ~> decision[p]

Properties == {Agree, CommitImpliesUnanimous, AbortJustified, Irreversible,
               Resolves, EveryoneDecides}

====