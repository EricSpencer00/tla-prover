---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

\* -------------------------------------------------
\* Type definitions
VoteSet == {yes, no}
DecisionSet == {commit, abort, undecided}
MsgState == {waiting, notsent}
Pid == participants

\* -------------------------------------------------
\* State variables
VARIABLES
    coordAlive,            \* TRUE iff coordinator is alive
    coordFaulty,           \* TRUE iff coordinator has crashed
    coordSentReq,          \* Set of participants to which the coordinator sent a vote request
    coordRecvVote,         \* Function [participants -> {"waiting"} \cup VoteSet]   (vote received or waiting)
    coordDecision,        \* ONE of commit, abort, undecided
    coordSentDecision,    \* Set of participants to which the decision has been broadcast

    partAlive,             \* Function [participants -> BOOLEAN] (TRUE iff that participant is alive)
    partFaulty,            \* Function [participants -> BOOLEAN] (TRUE iff that participant has crashed)
    partVote,              \* Function [participants -> VoteSet] (the vote chosen at init)
    partHasSentVote,       \* Set of participants that have already sent their vote
    partDecision           \* Function [participants -> DecisionSet]

\* -------------------------------------------------
\* Initial state
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordSentReq = {}
    /\ coordRecvVote = [p \in participants |-> waiting]
    /\ coordDecision = undecided
    /\ coordSentDecision = {}

    /\ partAlive = [p \in participants |-> TRUE]
    /\ partFaulty = [p \in participants |-> FALSE]
    /\ partVote = [p \in participants |-> IF RandomElement(VoteSet) = yes THEN yes ELSE no]  \* nondet choose
    /\ partHasSentVote = {}
    /\ partDecision = [p \in participants |-> undecided]

\* -------------------------------------------------
\* Actions

CoordSendReq(p) ==
    /\ p \in participants
    /\ coordAlive = TRUE
    /\ p \notin coordSentReq
    /\ coordSentReq' = coordSentReq \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordRecvVote, coordDecision,
                    coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partHasSentVote, partDecision>>

CoordRecvVote(p) ==
    /\ p \in participants
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ p \in coordSentReq
    /\ coordRecvVote[p] = waiting
    /\ p \in partHasSentVote
    /\ coordRecvVote' = [coordRecvVote EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq,
                    coordDecision, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partHasSentVote, partDecision>>

CoordDetectFault(p) ==
    /\ p \in participants
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ p \in coordSentReq
    /\ coordRecvVote[p] = waiting
    /\ partAlive[p] = FALSE
    /\ coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq,
                    coordRecvVote, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partHasSentVote, partDecision>>

CoordMakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = undecided
    /\ \A p \in participants: coordRecvVote[p] # waiting
    /\ coordDecision' = IF \A p \in participants: coordRecvVote[p] = yes
                         THEN commit
                         ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq,
                    coordRecvVote, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partHasSentVote, partDecision>>

CoordBroadcast(p) ==
    /\ p \in participants
    /\ coordAlive = TRUE
    /\ coordDecision \in {commit, abort}
    /\ p \notin coordSentDecision
    /\ coordSentDecision' = coordSentDecision \cup {p}
    /\ partDecision' = [partDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq,
                    coordRecvVote, coordDecision,
                    partAlive, partFaulty, partVote,
                    partHasSentVote>>

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordFaulty' = TRUE
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordSentReq, coordRecvVote, coordDecision,
                    coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partHasSentVote, partDecision>>

PartSendVote(p) ==
    /\ p \in participants
    /\ partAlive[p] = TRUE
    /\ p \in coordSentReq
    /\ p \notin partHasSentVote
    /\ partHasSentVote' = partHasSentVote \cup {p}
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq,
                    coordRecvVote, coordDecision, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partDecision>>

PartAbortOnVote(p) ==
    /\ p \in participants
    /\ partAlive[p] = TRUE
    /\ p \in partHasSentVote
    /\ partVote[p] = no
    /\ partDecision[p] = undecided
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq,
                    coordRecvVote, coordDecision, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partHasSentVote>>

PartAbortOnTimeout(p) ==
    /\ p \in participants
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ partDecision' = [partDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq,
                    coordRecvVote, coordDecision, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partHasSentVote>>

PartDecideFromBroadcast(p) ==
    /\ p \in participants
    /\ partAlive[p] = TRUE
    /\ partDecision[p] = undecided
    /\ p \in coordSentDecision
    /\ partDecision' = [partDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq,
                    coordRecvVote, coordDecision, coordSentDecision,
                    partAlive, partFaulty, partVote,
                    partHasSentVote>>

PartDie(p) ==
    /\ p \in participants
    /\ partAlive[p] = TRUE
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSentReq,
                    coordRecvVote, coordDecision, coordSentDecision,
                    partVote, partHasSentVote, partDecision>>

\* -------------------------------------------------
\* Next-state relation
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordRecvVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnVote(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* -------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<coordAlive, coordFaulty, coordSentReq,
                       coordRecvVote, coordDecision, coordSentDecision,
                       partAlive, partFaulty, partVote,
                       partHasSentVote, partDecision>>

\* -------------------------------------------------
\* Type invariant (helps TLC but is not the safety property we check)
TypeOK ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordSentReq \subseteq participants
    /\ coordRecvVote \in [participants -> (VoteSet \cup {waiting})]
    /\ coordDecision \in DecisionSet
    /\ coordSentDecision \subseteq participants
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partFaulty \in [participants -> BOOLEAN]
    /\ partVote \in [participants -> VoteSet]
    /\ partHasSentVote \subseteq participants
    /\ partDecision \in [participants -> DecisionSet]

\* -------------------------------------------------
\* Safety property AC1: Agreement / Consistency
AC1 ==
    \A p, q \in participants:
        (partDecision[p] = commit) => (partDecision[q] = commit)

\* -------------------------------------------------
\* Safety property AC2: Commit validity
AC2 ==
    \A p \in participants:
        (partDecision[p] = commit) => (\A q \in participants: partVote[q] = yes)

\* -------------------------------------------------
\* Safety property AC3: Abort validity
AC3 ==
    \A p \in participants:
        (partDecision[p] = abort) =>
            ( \E q \in participants: partVote[q] = no
              \/ \E q \in participants: partFaulty[q] = TRUE
              \/ coordFaulty = TRUE)

\* -------------------------------------------------
\* Safety property AC4: Irrevocability
AC4 ==
    \A p \in participants:
        (partDecision[p] = commit => [] (partDecision[p] = commit)) /\
        (partDecision[p] = abort  => [] (partDecision[p] = abort))

\* -------------------------------------------------
\* Combined safety invariant required by the cfg
TypeInv == TypeOK

\* The spec's safety invariant (the cfg lists AC1? AC2? etc.; we expose them)
Inv == AC1 /\ AC2 /\ AC3 /\ AC4

====