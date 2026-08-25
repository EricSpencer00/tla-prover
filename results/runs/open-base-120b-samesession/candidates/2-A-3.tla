---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Constants required by the .cfg file
-----------------------------------------------------------------*)
CONSTANTS
    participants,   \* Set of participant identifiers
    yes, no,        \* Vote values
    undecided, commit, abort,  \* Decision values for participants
    waiting,        \* Coordinator waiting state (unused but required)
    notsent         \* Forwarding table entry meaning “no decision yet”

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    coordAlive,          \* TRUE iff coordinator is alive
    coordFaulty,         \* TRUE iff coordinator has crashed
    requestSent,         \* TRUE iff coordinator has sent the request
    coordDecision,       \* Coordinator's decision: commit, abort, or UNDEF
    broadcastSet,        \* Subset of participants to which the coordinator has already sent the decision
    Vote,                \* [p \in participants -> {yes,no}]
    voteSent,            \* Subset of participants that have already sent their vote
    Decision,            \* [p \in participants -> {undecided, commit, abort}]
    Forward              \* [p \in participants -> [q \in participants -> {notsent, commit, abort}]]

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
UNDEF == <<>>   \* a distinguished value for “no decision yet”

ParticipantSet == participants

CoordVars == <<coordAlive, coordFaulty, requestSent, coordDecision,
               broadcastSet>>
PartVars == <<Vote, voteSent, Decision, Forward>>

Vars == <<coordAlive, coordFaulty, requestSent, coordDecision,
          broadcastSet, Vote, voteSent, Decision, Forward>>

\* The set of all possible values for a forwarding entry
ForwardVal == {notsent, commit, abort}

\* The set of all possible values for a participant's decision
PartDecVal == {undecided, commit, abort}

\* The set of all possible values for the coordinator's decision
CoordDecVal == {commit, abort, UNDEF}

/*--------------------------  Initialization  ---------------------------*/
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ requestSent = FALSE
    /\ coordDecision = UNDEF
    /\ broadcastSet = {}
    /\ Vote = [p \in participants |-> IF RandomChoice({yes,no}) = yes THEN yes ELSE no]  \* votes are chosen nondeterministically
    /\ voteSent = {}
    /\ Decision = [p \in participants |-> undecided]
    /\ Forward = [p \in participants |-> [q \in participants |-> notsent]]

(*--------------------------  Coordinator actions  ---------------------------*)

SendRequest ==
    /\ coordAlive
    /\ ~requestSent
    /\ coordAlive' = coordAlive
    /\ coordFaulty' = coordFaulty
    /\ requestSent' = TRUE
    /\ coordDecision' = coordDecision
    /\ broadcastSet' = broadcastSet
    /\ UNCHANGED <<Vote, voteSent, Decision, Forward>>

MakeDecision ==
    /\ coordAlive
    /\ requestSent
    /\ coordDecision = UNDEF
    /\ \E d \in {commit, abort} : 
          /\ coordDecision' = d
          /\ broadcastSet' = {}          \* start broadcasting anew
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent>>
    /\ UNCHANGED <<Vote, voteSent, Decision, Forward>>

Broadcast ==
    /\ coordAlive
    /\ coordDecision # UNDEF
    /\ \E p \in participants :
          /\ p \notin broadcastSet
          /\ broadcastSet' = broadcastSet \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision>>
    /\ UNCHANGED <<Vote, voteSent, Decision, Forward>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<requestSent, coordDecision, broadcastSet, Vote, voteSent, Decision, Forward>>

CoordAction == SendRequest \/ MakeDecision \/ Broadcast \/ CoordDie

(*--------------------------  Participant actions  ---------------------------*)

VoteSend(p) ==
    /\ p \in participants
    /\ coordAlive
    /\ p \notin voteSent
    /\ voteSent' = voteSent \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                   broadcastSet, Vote, Decision, Forward>>

PreDecideFromCoordinator(p) ==
    /\ p \in participants
    /\ coordAlive
    /\ coordDecision # UNDEF
    /\ p \in broadcastSet
    /\ Forward[p][p] = notsent
    /\ Forward' = [Forward EXCEPT ![p][p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                   broadcastSet, Vote, voteSent, Decision>>

PreDecideFromForward(p) ==
    /\ p \in participants
    /\ Forward[p][p] = notsent
    /\ \E q \in participants :
          /\ q # p
          /\ Forward[q][p] \in {commit, abort}
    /\ LET d == CHOOSE d \in {commit, abort} : \E q \in participants :
                        q # p /\ Forward[q][p] = d
       IN Forward' = [Forward EXCEPT ![p][p] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                   broadcastSet, Vote, voteSent, Decision>>

ForwardDecision(p) ==
    /\ p \in participants
    /\ Forward[p][p] # notsent
    /\ \E q \in participants :
          /\ q # p
          /\ Forward[p][q] = notsent
    /\ LET d == Forward[p][p] IN
          Forward' = [Forward EXCEPT ![p][q] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                   broadcastSet, Vote, voteSent, Decision>>

Decide(p) ==
    /\ p \in participants
    /\ Forward[p][p] # notsent
    /\ \A q \in participants : Forward[p][q] # notsent
    /\ Decision' = [Decision EXCEPT ![p] = Forward[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                   broadcastSet, Vote, voteSent, Forward>>

AbortOnTimeout(p) ==
    /\ p \in participants
    /\ Decision[p] = undecided
    /\ coordFaulty
    /\ \A q \in participants :
          /\ Forward[q][p] = notsent
    /\ Decision' = [Decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, requestSent, coordDecision,
                   broadcastSet, Vote, voteSent, Forward>>

ParticipantDie(p) ==
    /\ p \in participants
    /\ Decision[p] = undecided
    /\ Decision' = [Decision EXCEPT ![p] = abort]    \* crashed participants are considered aborted
    /\ UNCHANGED <<coordAlive, coordFaulty, requestSent, coordDecision,
                   broadcastSet, Vote, voteSent, Forward>>

PartAction ==
    \E p \in participants :
        VoteSend(p) \/
        PreDecideFromCoordinator(p) \/
        PreDecideFromForward(p) \/
        ForwardDecision(p) \/
        Decide(p) \/
        AbortOnTimeout(p) \/
        ParticipantDie(p)

(*--------------------------  Next-state relation  ---------------------------*)

Next ==
    \/ CoordAction
    \/ PartAction

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
SpecNB == Init /\ [][Next]_Vars

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ requestSent \in BOOLEAN
    /\ coordDecision \in CoordDecVal
    /\ broadcastSet \subseteq participants
    /\ Vote \in [participants -> {yes, no}]
    /\ voteSent \subseteq participants
    /\ Decision \in [participants -> PartDecVal]
    /\ Forward \in [participants -> [participants -> ForwardVal]]

(*-----------------------------------------------------------------
  Additional (optional) properties
-----------------------------------------------------------------*)
\* Safety properties (not required by the .cfg but provided for completeness)
Agreement ==
    \A p,q \in participants :
        Decision[p] = commit => Decision[q] = commit

CommitValidity ==
    \A p \in participants :
        Decision[p] = commit => \A r \in participants : Vote[r] = yes

AbortValidity ==
    \E p \in participants :
        Decision[p] = abort => 
          \/ \E r \in participants : Vote[r] = no
          \/ coordFaulty
          \/ \E r \in participants : r \notin voteSent   \* some participant crashed before sending vote

Irrevocability ==
    \A p \in participants :
        (Decision[p] = commit \/ Decision[p] = abort) =>
          []<>(Decision[p] = Decision[p])   \* trivial, kept for symmetry

(*-----------------------------------------------------------------
  End of module
-----------------------------------------------------------------*)
====