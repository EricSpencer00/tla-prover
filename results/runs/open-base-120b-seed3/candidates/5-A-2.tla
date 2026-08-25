---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    coordAlive,          \* BOOLEAN: coordinator is alive
    coordFaulty,         \* BOOLEAN: coordinator is faulty (crashed)
    coordSentReq,        \* SUBSET participants: vote requests already sent
    coordVotes,          \* [participants -> {yes,no,waiting}]: votes received or waiting
    coordDecision,       \* {undecided,commit,abort}: coordinator's decision
    coordSentDecision,   \* SUBSET participants: decision already broadcast to each participant
    alive,               \* SUBSET participants: participants currently alive
    faulty,              \* SUBSET participants: participants that have crashed
    vote,                \* [participants -> {yes,no}]: participants' original votes
    sentVote,            \* SUBSET participants: participants that have sent their vote
    decision             \* [participants -> {undecided,commit,abort}]: participants' final decision

vars == << coordAlive, coordFaulty, coordSentReq, coordVotes, coordDecision,
           coordSentDecision, alive, faulty, vote, sentVote, decision >>

\* ---------- Initial State ----------
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordSentReq = {}
    /\ coordVotes = [p \in participants |-> waiting]
    /\ coordDecision = undecided
    /\ coordSentDecision = {}
    /\ alive = participants
    /\ faulty = {}
    /\ \A p \in participants: vote[p] \in {yes, no}
    /\ sentVote = {}
    /\ decision = [p \in participants |-> undecided]

\* ---------- Coordinator Actions ----------
SendVoteReq(p) ==
    /\ coordAlive
    /\ p \notin coordSentReq
    /\ coordSentReq' = coordSentReq \cup {p}
    /\ UNCHANGED << coordVotes, coordDecision, coordSentDecision,
                   alive, faulty, vote, sentVote, decision, coordFaulty >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in coordSentReq
    /\ coordVotes[p] = waiting
    /\ p \in sentVote
    /\ coordVotes' = [coordVotes EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << coordAlive, coordFaulty, coordSentReq, coordDecision,
                   coordSentDecision, alive, faulty, vote, sentVote, decision >>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in coordSentReq
    /\ coordVotes[p] = waiting
    /\ p \notin alive               \* participant has crashed
    /\ coordDecision' = abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordSentReq, coordVotes,
                   coordSentDecision, alive, faulty, vote, sentVote, decision >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: coordVotes[p] \in {yes, no}
    /\ LET allYes == \A p \in participants: coordVotes[p] = yes
       IN coordDecision' = IF allYes THEN commit ELSE abort
    /\ UNCHANGED << coordAlive, coordFaulty, coordSentReq, coordVotes,
                   coordSentDecision, alive, faulty, vote, sentVote, decision >>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ p \in participants
    /\ p \notin coordSentDecision
    /\ coordSentDecision' = coordSentDecision \cup {p}
    /\ decision' = [decision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordSentReq, coordVotes,
                   coordDecision, alive, faulty, vote, sentVote >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << coordSentReq, coordVotes, coordDecision,
                   coordSentDecision, alive, faulty, vote, sentVote, decision >>

\* ---------- Participant Actions ----------
SendVote(p) ==
    /\ p \in alive
    /\ p \notin sentVote
    /\ p \in coordSentReq
    /\ sentVote' = sentVote \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordSentReq, coordVotes,
                   coordDecision, coordSentDecision, alive, faulty, vote, decision >>

AbortOnVote(p) ==
    /\ p \in alive
    /\ decision[p] = undecided
    /\ vote[p] = no
    /\ p \in sentVote
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordSentReq, coordVotes,
                   coordDecision, coordSentDecision, alive, faulty, vote, sentVote >>

AbortOnTimeout(p) ==
    /\ p \in alive
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ p \notin coordSentReq
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << coordAlive, coordFaulty, coordSentReq, coordVotes,
                   coordDecision, coordSentDecision, alive, faulty, vote, sentVote >>

DecideOnBroadcast(p) ==
    /\ p \in alive
    /\ decision[p] = undecided
    /\ p \in coordSentDecision
    /\ decision' = [decision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << coordAlive, coordFaulty, coordSentReq, coordVotes,
                   coordDecision, coordSentDecision, alive, faulty, vote, sentVote >>

ParticipantDie(p) ==
    /\ p \in alive
    /\ alive' = alive \ {p}
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED << coordAlive, coordFaulty, coordSentReq, coordVotes,
                   coordDecision, coordSentDecision, vote, sentVote, decision >>

\* ---------- Next-State Relation ----------
Next ==
    \/ \E p \in participants: SendVoteReq(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ \E p \in participants: BroadcastDecision(p)
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideOnBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)
    \/ CoordDie
    \/ MakeDecision

\* ---------- Specification ----------
Spec == Init /\ [][Next]_vars

\* ---------- Type Invariant ----------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordSentReq \subseteq participants
    /\ coordVotes \in [participants -> {yes, no, waiting}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordSentDecision \subseteq participants
    /\ alive \subseteq participants
    /\ faulty \subseteq participants
    /\ vote \in [participants -> {yes, no}]
    /\ sentVote \subseteq participants
    /\ decision \in [participants -> {undecided, commit, abort}]

\* ---------- Invariants ----------
INVARIANT TypeInv

====