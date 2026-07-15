---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Participant == participants
Decision    == {commit, abort}
Vote        == {yes, no}
ForwardStatus == {notsent, commit, abort}

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    coordAlive,          \* Boolean: coordinator is alive
    coordFaulty,         \* Boolean: coordinator is faulty (crashed)
    coordDecision,       \* Decision made by coordinator (or "none")
    coordBroadcasted,    \* Set of participants to which coordinator has sent its decision
    votes,               \* [p \in Participant -> Vote \cup {"none"}]
    participantAlive,    \* [p \in Participant -> BOOLEAN]
    participantFaulty,   \* [p \in Participant -> BOOLEAN]
    participantDecision, \* [p \in Participant -> Decision \cup {undecided}]
    forwarding,          \* [p \in Participant -> [q \in Participant -> ForwardStatus]]
    preDecided           \* [p \in Participant -> BOOLEAN]  \* true iff p has stored a pre‑decision

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
AllForwarded(p) == \A q \in Participant \ {p} : forwarding[p][q] # notsent

AnyAliveParticipantHasPreDecided ==
    \E p \in Participant : participantAlive[p] /\ preDecided[p]

AnyAliveParticipantHasDecision ==
    \E p \in Participant : participantAlive[p] /\ participantDecision[p] # undecided

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = "none"
    /\ coordBroadcasted = {}
    /\ votes = [p \in Participant |-> "none"]
    /\ participantAlive = [p \in Participant |-> TRUE]
    /\ participantFaulty = [p \in Participant |-> FALSE]
    /\ participantDecision = [p \in Participant |-> undecided]
    /\ forwarding = [p \in Participant |-> [q \in Participant |-> notsent]]
    /\ preDecided = [p \in Participant |-> FALSE]

(*--------------------------------------------------------------------
  Coordinator actions (inherited from ACP‑SB)
--------------------------------------------------------------------*)
CoordSendRequest ==
    /\ coordAlive
    /\ coordDecision = "none"
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, votes,
                    participantAlive, participantFaulty,
                    participantDecision, forwarding, preDecided>>

CoordCollectVotes ==
    /\ coordAlive
    /\ coordDecision = "none"
    /\ \A p \in Participant : votes[p] # "none"
    /\ coordDecision' = IF \A p \in Participant : votes[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordBroadcasted,
                    participantAlive, participantFaulty,
                    participantDecision, forwarding, preDecided, votes>>

CoordBroadcast ==
    /\ coordAlive
    /\ coordDecision # "none"
    /\ coordBroadcasted' = participants
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    votes, participantAlive, participantFaulty,
                    participantDecision, forwarding, preDecided>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordBroadcasted, votes,
                    participantAlive, participantFaulty,
                    participantDecision, forwarding, preDecided>>

(*--------------------------------------------------------------------
  Participant actions
--------------------------------------------------------------------*)
ParticipantSendVote(p) ==
    /\ participantAlive[p]
    /\ votes[p] = "none"
    /\ votes' = [votes EXCEPT ![p] = IF participantFaulty[p] THEN no ELSE yes]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, participantAlive,
                    participantFaulty, participantDecision,
                    forwarding, preDecided>>

PreDecideFromCoord(p) ==
    /\ participantAlive[p]
    /\ ~preDecided[p]
    /\ p \in coordBroadcasted
    /\ coordDecision # "none"
    /\ preDecided' = [preDecided EXCEPT ![p] = TRUE]
    /\ forwarding' = [forwarding EXCEPT ![p][p] = IF coordDecision = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, votes,
                    participantAlive, participantFaulty,
                    participantDecision>>

PreDecideFromForward(p) ==
    /\ participantAlive[p]
    /\ ~preDecided[p]
    /\ \E q \in Participant \ {p} :
          forwarding[q][p] # notsent
    /\ preDecided' = [preDecided EXCEPT ![p] = TRUE]
    /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[CHOOSE q \in Participant \ {p} : forwarding[q][p] # notsent][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, votes,
                    participantAlive, participantFaulty,
                    participantDecision>>

Forward(p, q) ==
    /\ participantAlive[p]
    /\ participantAlive[q]
    /\ preDecided[p]
    /\ forwarding[p][q] = notsent
    /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, votes,
                    participantAlive, participantFaulty,
                    participantDecision, preDecided>>

Decide(p) ==
    /\ participantAlive[p]
    /\ preDecided[p]
    /\ AllForwarded(p)
    /\ participantDecision' = [participantDecision EXCEPT ![p] = IF forwarding[p][p] = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, votes,
                    participantAlive, participantFaulty,
                    forwarding, preDecided>>

AbortOnTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordAlive
    /\ ~AnyAliveParticipantHasPreDecided
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, votes,
                    participantAlive, participantFaulty,
                    forwarding, preDecided>>

ParticipantDie(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    coordBroadcasted, votes,
                    participantDecision, forwarding, preDecided>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ CoordSendRequest
    \/ CoordCollectVotes
    \/ CoordBroadcast
    \/ CoordDie
    \/ \E p \in Participant : ParticipantSendVote(p)
    \/ \E p \in Participant : PreDecideFromCoord(p)
    \/ \E p \in Participant : PreDecideFromForward(p)
    \/ \E p \in Participant : \E q \in Participant \ {p} : Forward(p, q)
    \/ \E p \in Participant : Decide(p)
    \/ \E p \in Participant : AbortOnTimeout(p)
    \/ \E p \in Participant : ParticipantDie(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                         coordBroadcasted, votes,
                         participantAlive, participantFaulty,
                         participantDecision, forwarding, preDecided>>

(*--------------------------------------------------------------------
  Type invariant (ensures all variables stay within their domains)
--------------------------------------------------------------------*)
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {"none", commit, abort}
    /\ coordBroadcasted \subseteq Participant
    /\ votes \in [Participant -> (Vote \cup {"none"})]
    /\ participantAlive \in [Participant -> BOOLEAN]
    /\ participantFaulty \in [Participant -> BOOLEAN]
    /\ participantDecision \in [Participant -> (Decision \cup {undecided})]
    /\ forwarding \in [Participant -> [Participant -> ForwardStatus]]
    /\ preDecided \in [Participant -> BOOLEAN]

(*--------------------------------------------------------------------
  Safety properties (the invariants required by the description)
--------------------------------------------------------------------*)
(* AC1: Agreement *)
Agreement ==
    ~(\E p, q \in Participant :
          participantDecision[p] = commit /\ participantDecision[q] = abort)

(* AC2: Commit validity *)
CommitValidity ==
    ~(\E p \in Participant : participantDecision[p] = commit) \/
    \A p \in Participant : votes[p] = yes

(* AC3: Abort validity *)
AbortValidity ==
    ~(\E p \in Participant : participantDecision[p] = abort) \/
    (\E p \in Participant : votes[p] = no) \/
    (\E p \in Participant : participantFaulty[p]) \/
    coordFaulty

(* AC4: Irrevocability *)
Irrevocability ==
    \A p \in Participant :
        (participantDecision[p] = commit => 
            [] (participantDecision[p] = commit)) /\
        (participantDecision[p] = abort => 
            [] (participantDecision[p] = abort))

(*--------------------------------------------------------------------
  The set of invariants required by the .cfg file
--------------------------------------------------------------------*)
Inv == TypeInvNB

=============================================================================