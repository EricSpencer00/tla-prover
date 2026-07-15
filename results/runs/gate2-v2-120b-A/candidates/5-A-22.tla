---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

(* --derived constants-- *)
AllVotes == {yes, no}
AllDecisions == {commit, abort, undecided}
AllStatus == {waiting, notsent}

VARIABLES
    alive,            \* Set of alive processes (participants ∪ {coord})
    faulty,           \* Set of faulty processes (participants ∪ {coord})
    votes,            \* [p \in participants -> {yes, no}]
    sentVote,         \* [p \in participants -> BOOLEAN]  \* participant has sent vote
    decision,         \* [p \in participants -> AllDecisions]
    requestSent,      \* [p \in participants -> BOOLEAN]  \* coordinator sent vote request
    receivedVote,     \* [p \in participants -> AllVotes \cup {waiting}]
    broadcastSent,    \* [p \in participants -> BOOLEAN]  \* coordinator has broadcast decision
    coordDecision,    \* {commit, abort, undecided}
    coordAlive,       \* BOOLEAN
    coordFaulty       \* BOOLEAN

(* --Initialization-- *)
Init ==
    /\ alive = participants \cup {"coord"}
    /\ faulty = {}
    /\ votes = [p \in participants |-> IF RandomChoice({yes,no}) = 1 THEN yes ELSE no]
       \* RandomChoice is a placeholder; TLC will nondeterministically assign
    /\ sentVote = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ requestSent = [p \in participants |-> FALSE]
    /\ receivedVote = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> FALSE]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

(* --Helper predicates-- *)
AllRequestsSent == \A p \in participants: requestSent[p]
AllVotesReceived == \A p \in participants: receivedVote[p] # waiting
AllBroadcastSent == \A p \in participants: broadcastSent[p]

(* --Coordinator actions-- *)

CoordSendReq(p) ==
    /\ coordAlive
    /\ ~requestSent[p]
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, faulty, votes, sentVote, decision,
                    receivedVote, broadcastSent, coordDecision,
                    coordAlive, coordFaulty>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ requestSent[p]
    /\ receivedVote[p] = waiting
    /\ sentVote[p]
    /\ receivedVote' = [receivedVote EXCEPT ![p] = votes[p]]
    /\ UNCHANGED <<alive, faulty, votes, sentVote, decision,
                    requestSent, broadcastSent, coordDecision,
                    coordAlive, coordFaulty>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ requestSent[p]
    /\ receivedVote[p] = waiting
    /\ ~alive[p]           \* participant died without sending vote
    /\ coordDecision' = abort
    /\ coordDecision' \in {commit, abort}
    /\ UNCHANGED <<alive, faulty, votes, sentVote, decision,
                    requestSent, receivedVote, broadcastSent,
                    coordAlive, coordFaulty>>

CoordMakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ AllVotesReceived
    /\ IF \A p \in participants: receivedVote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<alive, faulty, votes, sentVote, decision,
                    requestSent, receivedVote, broadcastSent,
                    coordAlive, coordFaulty>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ ~broadcastSent[p]
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, faulty, votes, sentVote, decision,
                    requestSent, receivedVote, coordDecision,
                    coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<alive, faulty, votes, sentVote, decision,
                    requestSent, receivedVote, broadcastSent,
                    coordDecision, coordAlive, coordFaulty>>

(* --Participant actions-- *)

PartSendVote(p) ==
    /\ alive[p]
    /\ requestSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, faulty, votes, decision,
                    requestSent, receivedVote, broadcastSent,
                    coordDecision, coordAlive, coordFaulty>>

PartAbortOnNo(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ votes[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, faulty, votes, sentVote,
                    requestSent, receivedVote, broadcastSent,
                    coordDecision, coordAlive, coordFaulty>>

PartAbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~requestSent[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, faulty, votes, sentVote,
                    requestSent, receivedVote, broadcastSent,
                    coordDecision, coordAlive, coordFaulty>>

PartDecideFromBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ broadcastSent[p]
    /\ decision' = [decision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<alive, faulty, votes, sentVote,
                    requestSent, receivedVote, broadcastSent,
                    coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
    /\ alive[p]
    /\ alive' = alive \ {p}
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED <<sentVote, decision, requestSent,
                    receivedVote, broadcastSent,
                    coordDecision, coordAlive, coordFaulty>>

(* --Next-state relation-- *)

Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnNo(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

(* --Specification-- *)

Spec == Init /\ [][Next]_<<alive, faulty, votes, sentVote, decision,
                        requestSent, receivedVote, broadcastSent,
                        coordDecision, coordAlive, coordFaulty>>

(* --Type invariant (helps TLC, not the safety property required)*)

TypeInv ==
    /\ alive \subseteq participants \cup {"coord"}
    /\ faulty \subseteq participants \cup {"coord"}
    /\ votes \in [participants -> AllVotes]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ decision \in [participants -> AllDecisions]
    /\ requestSent \in [participants -> BOOLEAN]
    /\ receivedVote \in [participants -> (AllVotes \cup {waiting})]
    /\ broadcastSent \in [participants -> BOOLEAN]
    /\ coordDecision \in AllDecisions
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

(* --Safety properties-- *)

AC1 ==
    \A p,q \in participants:
        (decision[p] = commit) => (decision[q] # abort)

AC2 ==
    \A p \in participants:
        decision[p] = commit => \A q \in participants: votes[q] = yes

AC3 ==
    \A p \in participants:
        decision[p] = abort =>
            (\E q \in participants: votes[q] = no) \/
            (\E q \in participants: q \in faulty) \/
            ("coord" \in faulty)

AC4 ==
    \A p \in participants:
        (decision[p] = commit) => [] (decision[p] = commit) /\
        (decision[p] = abort)  => [] (decision[p] = abort)

(* The module must expose the names required by the .cfg file *)
SpecInv == AC1 /\ AC2 /\ AC3 /\ AC4

=============================================================================