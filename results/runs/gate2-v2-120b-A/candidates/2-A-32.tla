---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Participant == participants
Decision    == {commit, abort, undecided}
Vote        == {yes, no}
ForwardStatus == {notsent, commit, abort}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    coordAlive,          \* TRUE iff the coordinator is alive
    coordFaulty,         \* TRUE iff the coordinator is faulty (crashed)
    coordDecision,      \* Decision made by coordinator (undecided initially)
    participantsAlive,  \* Set of participants that are alive
    participantsFaulty, \* Set of participants that are faulty (crashed)
    votes,              \* [p \in participants |-> Vote] (participants' votes)
    forwarding,         \* [p \in participants |-> [q \in participants |-> ForwardStatus]]
    decided,            \* [p \in participants |-> Decision] (final decision, undecided initially)
    forwardedAll        \* [p \in participants |-> BOOLEAN] (has p forwarded to everyone?)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Other(p) == participants \ {p}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ participantsAlive = participants
    /\ participantsFaulty = {}
    /\ votes = [p \in participants |-> yes]               \* arbitrary; may be overridden by actions
    /\ forwarding = [p \in participants |-> [q \in participants |-> notsent]]
    /\ decided = [p \in participants |-> undecided]
    /\ forwardedAll = [p \in participants |-> FALSE]

\* ----------------------------------------------------------------------
\* Coordinator actions (inherited from ACP-SB)
\* ----------------------------------------------------------------------
CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordDecision' = IF \A p \in participantsAlive : votes[p] = yes
                         THEN commit
                         ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, participantsAlive,
                    participantsFaulty, votes, forwarding, decided,
                    forwardedAll>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, participantsAlive, participantsFaulty,
                    votes, forwarding, decided, forwardedAll>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
\* (1) Send vote to coordinator (not modeled explicitly, we just set votes)
VoteYes(p) ==
    /\ p \in participantsAlive
    /\ votes[p] = undecided
    /\ votes' = [votes EXCEPT ![p] = yes]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantsAlive, participantsFaulty,
                    forwarding, decided, forwardedAll>>

VoteNo(p) ==
    /\ p \in participantsAlive
    /\ votes[p] = undecided
    /\ votes' = [votes EXCEPT ![p] = no]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantsAlive, participantsFaulty,
                    forwarding, decided, forwardedAll>>

\* (2) Pre-decide from coordinator
PreDecideFromCoord(p) ==
    /\ p \in participantsAlive
    /\ forwarding[p][p] = notsent
    /\ coordDecision # undecided
    /\ forwarding' = [forwarding EXCEPT ![p][p] = IF coordDecision = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantsAlive, participantsFaulty,
                    votes, decided, forwardedAll>>

\* (3) Pre-decide from another participant
PreDecideFromForward(p) ==
    /\ p \in participantsAlive
    /\ forwarding[p][p] = notsent
    /\ \E q \in participantsAlive :
          /\ q # p
          /\ forwarding[q][p] # notsent
    /\ LET d == IF \E q \in participantsAlive :
                     forwarding[q][p] = commit
                     THEN commit
                     ELSE abort
       IN forwarding' = [forwarding EXCEPT ![p][p] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantsAlive, participantsFaulty,
                    votes, decided, forwardedAll>>

\* (4) Forward to a specific other participant
Forward(p, q) ==
    /\ p \in participantsAlive
    /\ q \in participantsAlive
    /\ q # p
    /\ forwarding[p][p] # notsent               \* p has a pre‑decision
    /\ forwarding[p][q] = notsent               \* not yet forwarded to q
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantsAlive, participantsFaulty,
                    votes, decided, forwardedAll>>

\* (5) Mark that p has finished forwarding to everyone
AllForwarded(p) ==
    /\ p \in participantsAlive
    /\ \A q \in participants : forwarding[p][q] # notsent
    /\ forwardedAll' = [forwardedAll EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantsAlive, participantsFaulty,
                    votes, forwarding, decided>>

\* (6) Decide (non‑blocking) once all forwarding done
Decide(p) ==
    /\ p \in participantsAlive
    /\ forwarding[p][p] # notsent
    /\ forwardedAll[p] = TRUE
    /\ decided[p] = undecided
    /\ decided' = [decided EXCEPT ![p] = IF forwarding[p][p] = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantsAlive, participantsFaulty,
                    votes, forwarding, forwardedAll>>

\* (7) Abort on timeout (coordinator dead, no broadcasts)
AbortTimeout(p) ==
    /\ p \in participantsAlive
    /\ decided[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participantsAlive : forwarding[q][p] = notsent
    /\ decided' = [decided EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantsAlive, participantsFaulty,
                    votes, forwarding, forwardedAll>>

\* (8) Participant crash
PartDie(p) ==
    /\ p \in participantsAlive
    /\ participantsAlive' = participantsAlive \ {p}
    /\ participantsFaulty' = participantsFaulty \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, forwarding, decided, forwardedAll>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participantsAlive : VoteYes(p)
    \/ \E p \in participantsAlive : VoteNo(p)
    \/ CoordMakeDecision
    \/ CoordDie
    \/ \E p \in participantsAlive : PreDecideFromCoord(p)
    \/ \E p \in participantsAlive : PreDecideFromForward(p)
    \/ \E p \in participantsAlive, q \in participantsAlive : Forward(p, q)
    \/ \E p \in participantsAlive : AllForwarded(p)
    \/ \E p \in participantsAlive : Decide(p)
    \/ \E p \in participantsAlive : AbortTimeout(p)
    \/ \E p \in participantsAlive : PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                        participantsAlive, participantsFaulty,
                        votes, forwarding, decided, forwardedAll>>

\* ----------------------------------------------------------------------
\* Safety Invariant (type correctness)
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in Decision
    /\ participantsAlive \subseteq participants
    /\ participantsFaulty \subseteq participants
    /\ participantsAlive \cap participantsFaulty = {}
    /\ votes \in [participants -> {yes, no, undecided}]
    /\ forwarding \in [participants -> [participants -> ForwardStatus]]
    /\ decided \in [participants -> Decision]
    /\ forwardedAll \in [participants -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Theorem (optional, can be used by TLC)
\* ----------------------------------------------------------------------
THEOREM SpecNB => []TypeInvNB

====