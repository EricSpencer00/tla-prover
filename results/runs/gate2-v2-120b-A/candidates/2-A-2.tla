---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  Constants (set values are provided by the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

(*--------------------------------------------------------------------
  Aliases for readability
--------------------------------------------------------------------*)
Participant == participants
Decision    == {commit, abort}
Vote        == {yes, no}
Message     == {"Req", "Vote", "Dec"}
FCStatus    == {notsent, commit, abort} \* forwarding table entry status

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    coordAlive,          \* TRUE iff coordinator is alive
    coordFaulty,         \* TRUE iff coordinator is faulty (crashed)
    coordDecision,       \* coordinator's decision (commit/abort) or UNDECIDED
    votes,               \* [p \in Participant -> Vote]   (what each participant voted)
    participantAlive,    \* [p \in Participant -> BOOLEAN] (alive status)
    participantFaulty,   \* [p \in Participant -> BOOLEAN] (faulty flag)
    participantDecision, \* [p \in Participant -> {"undecided", "commit", "abort"}]
    forwarding,          \* [p \in Participant -> [q \in Participant -> FCStatus]]
    coordSent             \* [p \in Participant -> BOOLEAN]  (has coordinator broadcast to p)

(*--------------------------------------------------------------------
  Type invariant (used as the exported safety invariant)
--------------------------------------------------------------------*)
TypeInvNB ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {commit, abort, "undecided"}
  /\ votes \in [Participant -> Vote]
  /\ participantAlive \in [Participant -> BOOLEAN]
  /\ participantFaulty \in [Participant -> BOOLEAN]
  /\ participantDecision \in [Participant -> {"undecided", "commit", "abort"}]
  /\ forwarding \in [Participant -> [Participant -> FCStatus]]
  /\ coordSent \in [Participant -> BOOLEAN]

(*--------------------------------------------------------------------
  Initial predicate
--------------------------------------------------------------------*)
Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = "undecided"
  /\ votes = [p \in Participant |-> yes]       \* arbitrary initial vote; model will explore
  /\ participantAlive = [p \in Participant |-> TRUE]
  /\ participantFaulty = [p \in Participant |-> FALSE]
  /\ participantDecision = [p \in Participant |-> "undecided"]
  /\ forwarding = [p \in Participant |-> [q \in Participant |-> notsent]]
  /\ coordSent = [p \in Participant |-> FALSE]

(*--------------------------------------------------------------------
  Coordinator actions
--------------------------------------------------------------------*)

CoordDie ==
  /\ coordAlive = TRUE
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordDecision, votes, participantAlive,
                 participantFaulty, participantDecision,
                 forwarding, coordSent>>

CoordMakeDecision ==
  /\ coordAlive = TRUE
  /\ coordDecision = "undecided"
  /\ coordDecision' \in Decision
  /\ UNCHANGED <<coordAlive, coordFaulty, votes,
                 participantAlive, participantFaulty,
                 participantDecision, forwarding, coordSent>>

CoordBroadcast ==
  /\ coordAlive = TRUE
  /\ coordDecision \in Decision
  /\ \E p \in Participant :
        /\ participantAlive[p] = TRUE
        /\ coordSent[p] = FALSE
        /\ coordSent' = [coordSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                 votes, participantAlive, participantFaulty,
                 participantDecision, forwarding>>

(*--------------------------------------------------------------------
  Participant actions
--------------------------------------------------------------------*)

SendVote(p) ==
  /\ participantAlive[p] = TRUE
  /\ participantFaulty[p] = FALSE
  /\ votes' = [votes EXCEPT ![p] = IF votes[p] = yes THEN yes ELSE no]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                 participantAlive, participantFaulty,
                 participantDecision, forwarding, coordSent>>

PreDecideFromCoord(p) ==
  /\ participantAlive[p] = TRUE
  /\ participantDecision[p] = "undecided"
  /\ coordAlive = TRUE
  /\ coordSent[p] = TRUE
  /\ forwarding[p][p] = notsent
  /\ forwarding' = [forwarding EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                 votes, participantAlive, participantFaulty,
                 participantDecision, coordSent>>

PreDecideFromForward(p) ==
  /\ participantAlive[p] = TRUE
  /\ participantDecision[p] = "undecided"
  /\ forwarding[p][p] = notsent
  /\ \E q \in Participant :
        /\ q # p
        /\ forwarding[q][p] # notsent
        /\ forwarding' = [forwarding EXCEPT ![p][p] = forwarding[q][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                 votes, participantAlive, participantFaulty,
                 participantDecision, coordSent>>

Forward(p) ==
  /\ participantAlive[p] = TRUE
  /\ forwarding[p][p] # notsent
  /\ \E q \in Participant :
        /\ q # p
        /\ forwarding[p][q] = notsent
        /\ forwarding' = [forwarding EXCEPT ![p][q] = forwarding[p][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                 votes, participantAlive, participantFaulty,
                 participantDecision, coordSent>>

Decide(p) ==
  /\ participantAlive[p] = TRUE
  /\ forwarding[p][p] # notsent
  /\ \A q \in Participant : q # p => forwarding[p][q] # notsent
  /\ participantDecision[p] = "undecided"
  /\ participantDecision' = [participantDecision EXCEPT ![p] = forwarding[p][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                 votes, participantAlive, participantFaulty,
                 forwarding, coordSent>>

AbortOnTimeout(p) ==
  /\ participantAlive[p] = TRUE
  /\ participantDecision[p] = "undecided"
  /\ coordAlive = FALSE
  /\ \A q \in Participant : ~(coordSent[q] = TRUE)   \* coordinator never sent to a live participant
  /\ \A q \in Participant :
        ( participantAlive[q] = FALSE ) =>
           \A r \in Participant :
               forwarding[q][r] = notsent               \* no dead participant forwarded anything
  /\ participantDecision' = [participantDecision EXCEPT ![p] = "abort"]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                 votes, participantAlive, participantFaulty,
                 forwarding, coordSent>>

ParticipantDie(p) ==
  /\ participantAlive[p] = TRUE
  /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
  /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                 votes, participantDecision, forwarding, coordSent>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
  \/ \E p \in Participant : SendVote(p)
  \/ \E p \in Participant : ParticipantDie(p)
  \/ \E p \in Participant : PreDecideFromCoord(p)
  \/ \E p \in Participant : PreDecideFromForward(p)
  \/ \E p \in Participant : Forward(p)
  \/ \E p \in Participant : Decide(p)
  \/ \E p \in Participant : AbortOnTimeout(p)
  \/ CoordMakeDecision
  \/ CoordBroadcast
  \/ CoordDie

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                         votes, participantAlive, participantFaulty,
                         participantDecision, forwarding, coordSent>>

(*--------------------------------------------------------------------
  The identifier required by the .cfg file as the safety invariant
--------------------------------------------------------------------*)
THE_INVARIANT == TypeInvNB

====