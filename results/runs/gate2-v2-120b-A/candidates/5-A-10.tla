---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, FiniteSets

\* ------------------------------------------------------------
\* Constants (must be supplied in the .cfg file)
\* ------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

\* ------------------------------------------------------------
\* State variables
\* ------------------------------------------------------------
VARIABLES
    coordAlive,        \* TRUE iff the coordinator is alive
    coordDec,          \* coordinator decision (undecided, commit, abort)
    coordSentReq,      \* set of participants to which a vote request has been sent
    coordRecvVote,     \* [p \in participants |-> waiting] or yes/no
    coordSentDec,      \* [p \in participants |-> notsent] or commit/abort

VARIABLES
    partAlive,         \* [p \in participants |-> BOOLEAN]  alive flag
    partVote,          \* [p \in participants |-> yes \/ no]
    partSentVote,      \* [p \in participants |-> BOOLEAN]  vote already sent?
    partDec            \* [p \in participants |-> undecided \/ commit \/ abort]

\* ------------------------------------------------------------
\* Type definitions (helpful for debugging, but not part of the required
\* invariant – they are used only for the TypeInv invariant)
\* ------------------------------------------------------------
VoteSet  == {yes, no}
DecSet   == {undecided, commit, abort}
ReqSet   == participants
RecvSet  == {waiting} \cup VoteSet
SentSet  == {notsent} \cup DecSet

\* ------------------------------------------------------------
\* Initialization
\* ------------------------------------------------------------
Init ==
    /\ coordAlive = TRUE
    /\ coordDec   = undecided
    /\ coordSentReq = {}
    /\ coordRecvVote = [p \in participants |-> waiting]
    /\ coordSentDec = [p \in participants |-> notsent]
    /\ partAlive   = [p \in participants |-> TRUE]
    /\ partVote    = [p \in participants |-> CHOOSE v \in VoteSet : TRUE]
    /\ partSentVote = [p \in participants |-> FALSE]
    /\ partDec      = [p \in participants |-> undecided]

\* ------------------------------------------------------------
\* Helper predicates
\* ------------------------------------------------------------
AllVotesReceived ==
    \A p \in participants: coordRecvVote[p] # waiting

AllDecisionsBroadcast ==
    \A p \in participants: coordSentDec[p] # notsent

AllPartsDecided ==
    \A p \in participants: partDec[p] # undecided

\* ------------------------------------------------------------
\* Coordinator actions
\* ------------------------------------------------------------
CoordSendReq(p) ==
    /\ coordAlive
    /\ p \in participants
    /\ p \notin coordSentReq
    /\ coordSentReq' = coordSentReq \cup {p}
    /\ UNCHANGED <<coordDec, coordRecvVote, coordSentDec,
                    partAlive, partVote, partSentVote, partDec>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ coordDec = undecided
    /\ p \in participants
    /\ p \in coordSentReq
    /\ coordRecvVote[p] = waiting
    /\ partAlive[p]
    /\ partSentVote[p]
    /\ coordRecvVote' = [coordRecvVote EXCEPT ![p] = partVote[p]]
    /\ UNCHANGED <<coordAlive, coordDec, coordSentReq,
                    coordSentDec, partAlive, partVote,
                    partSentVote, partDec>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDec = undecided
    /\ p \in participants
    /\ p \in coordSentReq
    /\ coordRecvVote[p] = waiting
    /\ ~partAlive[p]               \* participant crashed before sending vote
    /\ coordDec' = abort
    /\ UNCHANGED <<coordAlive, coordSentReq, coordRecvVote,
                    coordSentDec, partAlive, partVote,
                    partSentVote, partDec>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDec = undecided
    /\ AllVotesReceived
    /\ coordDec' = IF \A p \in participants: coordRecvVote[p] = yes
                   THEN commit
                   ELSE abort
    /\ UNCHANGED <<coordAlive, coordSentReq, coordRecvVote,
                    coordSentDec, partAlive, partVote,
                    partSentVote, partDec>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDec # undecided
    /\ p \in participants
    /\ coordSentDec[p] = notsent
    /\ coordSentDec' = [coordSentDec EXCEPT ![p] = coordDec]
    /\ UNCHANGED <<coordAlive, coordDec, coordSentReq,
                    coordRecvVote, partAlive, partVote,
                    partSentVote, partDec>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<coordDec, coordSentReq, coordRecvVote,
                    coordSentDec, partAlive, partVote,
                    partSentVote, partDec>>

\* ------------------------------------------------------------
\* Participant actions
\* ------------------------------------------------------------
PartSendVote(p) ==
    /\ partAlive[p]
    /\ p \in coordSentReq
    /\ ~partSentVote[p]
    /\ partSentVote' = [partSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordDec, coordSentReq,
                    coordRecvVote, coordSentDec,
                    partAlive, partVote,
                    partDec>>

PartAbortOnVote(p) ==
    /\ partAlive[p]
    /\ partDec[p] = undecided
    /\ partSentVote[p]
    /\ partVote[p] = no
    /\ partDec' = [partDec EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDec, coordSentReq,
                    coordRecvVote, coordSentDec,
                    partAlive, partVote,
                    partSentVote>>

PartAbortOnTimeout(p) ==
    /\ partAlive[p]
    /\ partDec[p] = undecided
    /\ ~coordAlive
    /\ ~p \in coordSentReq          \* coordinator never sent request
    /\ partDec' = [partDec EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordDec, coordSentReq,
                    coordRecvVote, coordSentDec,
                    partAlive, partVote,
                    partSentVote>>

PartDecideFromCoord(p) ==
    /\ partAlive[p]
    /\ partDec[p] = undecided
    /\ coordSentDec[p] # notsent
    /\ partDec' = [partDec EXCEPT ![p] = coordSentDec[p]]
    /\ UNCHANGED <<coordAlive, coordDec, coordSentReq,
                    coordRecvVote, coordSentDec,
                    partAlive, partVote,
                    partSentVote>>

PartDie(p) ==
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<coordAlive, coordDec, coordSentReq,
                    coordRecvVote, coordSentDec,
                    partVote, partSentVote, partDec>>

\* ------------------------------------------------------------
\* Next-state relation
\* ------------------------------------------------------------
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnVote(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideFromCoord(p)
    \/ \E p \in participants: PartDie(p)

\* ------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------
Spec == Init /\ [][Next]_<<coordAlive, coordDec, coordSentReq,
                        coordRecvVote, coordSentDec,
                        partAlive, partVote,
                        partSentVote, partDec>>

\* ------------------------------------------------------------
\* Type invariant (required)
\* ------------------------------------------------------------
TypeInv ==
    /\ coordAlive \in BOOLEAN
    /\ coordDec  \in DecSet
    /\ coordSentReq \subseteq participants
    /\ coordRecvVote \in [participants -> RecvSet]
    /\ coordSentDec  \in [participants -> SentSet]
    /\ partAlive \in [participants -> BOOLEAN]
    /\ partVote  \in [participants -> VoteSet]
    /\ partSentVote \in [participants -> BOOLEAN]
    /\ partDec \in [participants -> DecSet]

\* ------------------------------------------------------------
\* Safety invariants derived from the description
\* ------------------------------------------------------------

(* AC1: No two participants decide differently *)
Consistent ==
    \A p, q \in participants:
        (partDec[p] = commit => partDec[q] # abort) /\
        (partDec[p] = abort  => partDec[q] # commit)

(* AC2: Commit validity *)
CommitValid ==
    \A p \in participants:
        partDec[p] = commit => \A q \in participants: partVote[q] = yes

(* AC3: Abort validity *)
AbortValid ==
    \A p \in participants:
        partDec[p] = abort =>
            (\E q \in participants: partVote[q] = no) \/
            (\E q \in participants: ~partAlive[q]) \/
            ~coordAlive

(* AC4: Irrevocability *)
Irrevocable ==
    \A p \in participants:
        (partDec[p] = commit => [] (partDec[p] = commit)) /\
        (partDec[p] = abort  => [] (partDec[p] = abort))

\* ------------------------------------------------------------
\* The invariants exported (the .cfg asks for TypeInv only,
\* but we expose the safety invariants as well)
\* ------------------------------------------------------------
INVARIANTS Consistent, CommitValid, AbortValid, Irrevocable, TypeInv

====