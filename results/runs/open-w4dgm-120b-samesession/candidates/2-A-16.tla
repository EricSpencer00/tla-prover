---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

(* Non-blocking atomic commitment with a reliable broadcast and forwarding. *)
(* This extends the simple broadcast variant (ACP-SB) by adding a          *)
(* participant-to-participant forwarding table.  A participant stores a    *)
(* pre-decision it receives (from the coordinator or from a peer) in its  *)
(* own table entry, forwards it to every other participant, and only then  *)
(* finalizes its own decision.  This guarantees that a non-faulty           *)
(* participant always eventually decides, even if the coordinator crashes   *)
(* mid-broadcast.                                                            *)

CONSTANT participants, yes, no, undecided, commit, abort, waiting, notsent

\* A participant's forwarding table: what pre-decision it has stored at    *)
(* each index (its own, and the forwarding slots for every peer), plus    *)
(* which participants it has already forwarded to.                         *)
Participant == { p \in participants :
    vote : {"no", "yes", "undecided"},
    alive : BOOLEAN,
    decision : {undecided, commit, abort},
    faulty : BOOLEAN,
    voteSent : BOOLEAN,
    fwd : [ participants -> {notsent, yes, no} ],
    forwarded : { participants }
}

Coordinator == { p \in participants :
    decision : {undecided, commit, abort},
    alive : BOOLEAN,
    faulty : BOOLEAN,
    votes : { "none", "yes", "no", "mixed", "all_yes" }
}

Coord == CHOOSE c \in Coordinator : TRUE

VARIABLES participantsVar, coord

vars == << participantsVar, coord >>

TypeInvNB ==
    /\ participantsVar \in Participant
    /\ coord \in Coordinator
    /\ \A p \in participantsVar :
        /\ p.vote \in { "no", "yes", "undecided" }
        /\ p.alive \in BOOLEAN
        /\ p.decision \in {undecided, commit, abort}
        /\ p.faulty \in BOOLEAN
        /\ p.voteSent \in BOOLEAN
        /\ p.fwd \in [ participants -> {notsent, yes, no} ]
        /\ p.forwarded \subseteq participants

Init ==
    /\ participantsVar = { p \in participants :
        [ vote |-> "undecided", alive |-> TRUE, decision |-> undecided,
          faulty |-> FALSE, voteSent |-> FALSE,
          fwd |-> [ q \in participants |-> notsent ],
          forwarded |-> {} ] }
    /\ coord = [ decision |-> undecided, alive |-> TRUE, faulty |-> FALSE, votes |-> "none" ]

\* Coordinator sends a fresh request, resetting its tallied votes.
SendRequest ==
    /\ coord.alive
    /\ coord.decision = undecided
    /\ \A p \in participantsVar : p.vote = "undecided"
    /\ coord' = [ coord EXCEPT !.votes = "none" ]
    /\ UNCHANGED participantsVar

\* A live participant whose vote has not yet been sent casts a yes/no.
CastVote(p) ==
    /\ p \in participantsVar
    /\ p.alive
    /\ ~p.voteSent
    /\ coord.alive
    /\ p' = [ p EXCEPT !.vote = IF p.vote = "undecided" THEN "yes" ELSE "no", !.voteSent = TRUE ]
    /\ UNCHANGED << participantsVar, coord >>

\* The coordinator tallies every live participant's vote.
Tally(c) ==
    /\ c = coord
    /\ coord.alive
    /\ coord.decision = undecided
    /\ coord.votes = "none"
    /\ \A p \in participantsVar : p.vote # "undecided"
    /\ coord' = [ coord EXCEPT !.votes =
        IF \A p \in participantsVar : p.vote = "yes" THEN "all_yes"
        ELSE IF \E p \in participantsVar : p.vote = "no" THEN "no"
        ELSE "mixed" ]
    /\ UNCHANGED participantsVar

\* The coordinator detects at most one silent fault among the participants.
DetectFault ==
    /\ coord.alive
    /\ coord.votes \in { "none", "all_yes", "no", "mixed" }
    /\ coord.decision = undecided
    /\ \E p \in participantsVar : ~p.alive
    /\ coord' = [ coord EXCEPT !.faulty = TRUE ]
    /\ UNCHANGED participantsVar

\* The coordinator, if alive, broadcasts its decision to a participant.
Broadcast(c, p) ==
    /\ c = coord
    /\ coord.alive
    /\ coord.decision = undecided
    /\ coord.votes = "all_yes"
    /\ p \in participantsVar
    /\ p.alive
    /\ p.fwd[p] = notsent
    /\ coord' = [ coord EXCEPT !.decision = commit ]
    /\ participantsVar' = [ participantsVar EXCEPT ![p].fwd[p] = commit ]
    /\ UNCHANGED << >>

\* A participant records a pre-decision broadcast to it by the coordinator.
PreDecideFromCoord(p) ==
    /\ p \in participantsVar
    /\ p.alive
    /\ p.fwd[p] = notsent
    /\ coord.decision # undecided
    /\ coord.alive
    /\ participantsVar' = [ participantsVar EXCEPT ![p].fwd[p] = coord.decision ]
    /\ UNCHANGED coord

\* A participant records a pre-decision forwarded to it by another participant.
PreDecideFromPeer(p, q) ==
    /\ p \in participantsVar
    /\ p.alive
    /\ p.fwd[p] = notsent
    /\ q \in participantsVar
    /\ q.alive
    /\ p \in q.forwarded
    /\ participantsVar' = [ participantsVar EXCEPT ![p].fwd[p] = q.fwd[p] ]
    /\ UNCHANGED coord

\* A participant forwards its pre-decision to another participant that has not
\* yet received it.
Forward(p, q) ==
    /\ p \in participantsVar
    /\ p.alive
    /\ p.fwd[p] # notsent
    /\ q \in participantsVar
    /\ q.alive
    /\ q \notin p.forwarded
    /\ participantsVar' = [ participantsVar EXCEPT ![p].forwarded = @ \cup { q } ]
    /\ participantsVar' = [ participantsVar EXCEPT ![q].fwd[p] = p.fwd[p] ]

\* Once a participant has forwarded its pre-decision to everyone else, it
\* finalizes its own decision to match.
Decide(p) ==
    /\ p \in participantsVar
    /\ p.alive
    /\ p.fwd[p] # notsent
    /\ p.decision = undecided
    /\ p.forwarded = participants
    /\ p' = [ p EXCEPT !.decision = IF p.fwd[p] = commit THEN commit ELSE abort ]
    /\ UNCHANGED << participantsVar, coord >>

\* An undecided, alive participant aborts when the coordinator is dead and no
\* participant can still supply a decision (no broadcast in flight and no dead
\* participant left to forward one).
AbortOnTimeout(p) ==
    /\ p \in participantsVar
    /\ p.alive
    /\ p.decision = undecided
    /\ ~coord.alive
    /\ \A q \in participantsVar : q.fwd[p] = notsent
    /\ \A q \in participantsVar : q.alive => q.fwd[q] = notsent
    /\ p' = [ p EXCEPT !.decision = abort ]
    /\ UNCHANGED << participantsVar, coord >>

\* A participant crashes silently and becomes faulty.
Die(p) ==
    /\ p \in participantsVar
    /\ p.alive
    /\ participantsVar' = [ participantsVar EXCEPT ![p].alive = FALSE, !.faulty = TRUE ]
    /\ UNCHANGED coord

\* The coordinator may die silently while participants are still voting.
CoordDie ==
    /\ coord.alive
    /\ coord' = [ coord EXCEPT !.alive = FALSE, !.faulty = TRUE ]
    /\ UNCHANGED participantsVar

\* Coordinator progress: request, tally, broadcast.
CoordAct == SendRequest \/ Tally(coord) \/ DetectFault \/ CoordDie

\* Participant progress: vote, forward, pre-decide, decide, abort, die.
PartAct == \E p \in participantsVar : CastVote(p) \/ PreDecideFromCoord(p)
    \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)

Next == CoordAct \/ PartAct
        \/ \E p, q \in participantsVar : PreDecideFromPeer(p, q) \/ Forward(p, q)

SpecNB == Init /\ [][Next]_vars /\ WF_vars(PartAct) /\ WF_vars(CoordAct)

(* SAFETY PROPERTY: no two participants ever reach different decisions. *)
Agreement ==
    \A p, q \in participantsVar :
        (p.decision = commit /\ q.decision = abort) => FALSE

(* SAFETY PROPERTY: committing requires a unanimous yes. *)
CommitValidity ==
    (\E p \in participantsVar : p.decision = commit) =>
        (\A q \in participantsVar : q.vote = "yes")

(* SAFETY PROPERTY: aborting is always defensible. *)
AbortValidity ==
    (\E p \in participantsVar : p.decision = abort) =>
        (\E q \in participantsVar : q.vote = "no" \/ q.faulty \/ coord.faulty)

(* SAFETY PROPERTY: an irreversible decision is final. *)
Irreversible ==
    \A p \in participantsVar :
        (p.decision = commit \/ p.decision = abort) => (p' \in participantsVar => p'.decision = p.decision)

(* LIVENESS PROPERTY: every non-faulty participant eventually decides. *)
EventualDecision ==
    \A p \in participantsVar : (p.alive) ~> (p.decision # undecided)

(\* The base atomic-commit protocol always reaches a decision or finds a     *)
(* fault; the reliable broadcast is what keeps it non-blocking for all      *)
(* non-faulty participants.                                                  *)
Resolution == <>(\A p \in participantsVar : p.decision # undecided \/ coord.faulty)

(* STATE-CONSTRAINT: every participant's forwarding table stays within its *)
(* own vote domain plus the not-sent marker.                                 *)
TypeInvNB2 == \A p \in participantsVar : \A q \in participants : p.fwd[q] \in { notsent, yes, no }

\* RESERVED: Acceptor-bound realtime bound; NOP.
AcceptBound == TRUE

(\* LIVENESS PROPERTY: the non-blocking guarantee: every non-faulty         *)
(* participant eventually reaches a decision.                               *)
Termination == \A p \in participantsVar : p.alive ~> (p.decision # undecided)

====