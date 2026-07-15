---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Constants (to be supplied in the .cfg file)                             *)
(***************************************************************************)
CONSTANTS participants, yes, no, undecided, commit, abort,
          waiting, notsent

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)
VARIABLES 
    pVote,          \* vote chosen by each participant (yes or no)
    pAlive,         \* TRUE if participant is alive, FALSE if crashed
    pDecision,      \* participant's final decision (undecided, commit, abort)
    pSent           \* TRUE if participant has already sent its vote

VARIABLES
    cAlive,         \* TRUE if coordinator is alive
    cFaulty,        \* TRUE if coordinator has crashed
    cRequested,     \* set of participants to which a vote request has been sent
    cReceived,      \* mapping participant -> vote or waiting
    cDecision,      \* coordinator's decision (undecided, commit, abort)
    cSentDec        \* set of participants to which the decision has been broadcast

(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)
ParticipantSet == participants

\* The set of possible votes
VoteSet == {yes, no}

\* The set of possible final decisions for participants
PartDecSet == {undecided, commit, abort}

\* The set of possible states for the coordinator's decision
CoordDecSet == {undecided, commit, abort}

\* Mapping from participants to a default value
DefaultMap(set, val) == [p \in set |-> val]

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ pVote      = DefaultMap(participants, yes)  \* will be overridden nondeterministically
    /\ pAlive     = [p \in participants |-> TRUE]
    /\ pDecision  = DefaultMap(participants, undecided)
    /\ pSent      = DefaultMap(participants, FALSE)
    /\ cAlive     = TRUE
    /\ cFaulty    = FALSE
    /\ cRequested = {}
    /\ cReceived  = DefaultMap(participants, waiting)
    /\ cDecision  = undecided
    /\ cSentDec   = {}

\* Nondeterministically choose each participant's vote (yes or no)
ChooseVotes ==
    /\ pVote \in [p \in participants |-> VoteSet]

Init == Init /\ ChooseVotes

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* --- Coordinator actions -----------------------------------------------

CoordSendReq(p) ==
    /\ cAlive
    /\ p \in participants
    /\ p \notin cRequested
    /\ cRequested' = cRequested \cup {p}
    /\ UNCHANGED <<cAlive, cFaulty, cReceived, cDecision, cSentDec,
                    pVote, pAlive, pDecision, pSent>>

CoordReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ p \in participants
    /\ p \in cRequested
    /\ cReceived[p] = waiting
    /\ pSent[p] = TRUE
    /\ cReceived' = [cReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<cAlive, cFaulty, cRequested, cDecision, cSentDec,
                    pVote, pAlive, pDecision, pSent>>

CoordDetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ p \in participants
    /\ p \in cRequested
    /\ cReceived[p] = waiting
    /\ pAlive[p] = FALSE
    /\ cDecision' = abort
    /\ UNCHANGED <<cAlive, cFaulty, cRequested, cReceived, cSentDec,
                    pVote, pAlive, pDecision, pSent>>

CoordMakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants: cReceived[p] # waiting
    /\ IF \A p \in participants: cReceived[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED <<cAlive, cFaulty, cRequested, cReceived, cSentDec,
                    pVote, pAlive, pDecision, pSent>>

CoordBroadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ p \in participants
    /\ p \notin cSentDec
    /\ cSentDec' = cSentDec \cup {p}
    /\ pDecision' = [pDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<cAlive, cFaulty, cRequested, cReceived, cDecision,
                    pVote, pAlive, pSent>>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<cRequested, cReceived, cDecision, cSentDec,
                    pVote, pAlive, pDecision, pSent>>

\* --- Participant actions -----------------------------------------------

PartSendVote(p) ==
    /\ pAlive[p] = TRUE
    /\ p \in cRequested
    /\ pSent[p] = FALSE
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cFaulty, cRequested, cReceived, cDecision,
                    cSentDec, pVote, pAlive, pDecision>>

PartAbortOnNo(p) ==
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ pSent[p] = TRUE
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<cAlive, cFaulty, cRequested, cReceived, cDecision,
                    cSentDec, pVote, pAlive, pSent>>

PartAbortOnNoReq(p) ==
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ p \notin cRequested
    /\ cFaulty = TRUE
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<cAlive, cFaulty, cRequested, cReceived, cDecision,
                    cSentDec, pVote, pAlive, pSent>>

PartDecideOnBroadcast(p) ==
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ p \in cSentDec
    /\ pDecision' = [pDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<cAlive, cFaulty, cRequested, cReceived, cDecision,
                    cSentDec, pVote, pAlive, pSent>>

PartDie(p) ==
    /\ pAlive[p] = TRUE
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<cAlive, cFaulty, cRequested, cReceived, cDecision,
                    cSentDec, pVote, pDecision, pSent>>

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnNo(p)
    \/ \E p \in participants: PartAbortOnNoReq(p)
    \/ \E p \in participants: PartDecideOnBroadcast(p)
    \/ \E p \in participants: PartDie(p)

Spec == Init /\ [][Next]_<<cAlive, cFaulty, cRequested, cReceived,
                     cDecision, cSentDec,
                     pVote, pAlive, pDecision, pSent>>

(***************************************************************************)
(* Type correctness invariant (optional but useful)                        *)
(***************************************************************************)
TypeInv ==
    /\ pVote \in [participants -> VoteSet]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> PartDecSet]
    /\ pSent \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cRequested \subseteq participants
    /\ cReceived \in [participants -> (VoteSet \cup {waiting})]
    /\ cDecision \in CoordDecSet
    /\ cSentDec \subseteq participants

(***************************************************************************)
(* Safety invariants (derived from the description)                        *)
(***************************************************************************)

(* AC1: No two participants decide differently *)
ConsistentDecisions ==
    \A p, q \in participants :
        (pDecision[p] = commit  => pDecision[q] = commit) /\
        (pDecision[p] = abort   => pDecision[q] = abort)  /\
        (pDecision[p] = undecided => TRUE)

(* AC2: If any participant decides commit, all participants voted yes *)
CommitValidity ==
    \A p \in participants :
        (pDecision[p] = commit) => \A q \in participants : pVote[q] = yes

(* AC3: If any participant decides abort, then at least one participant voted no,
        or at least one participant is faulty, or the coordinator is faulty *)
AbortValidity ==
    \A p \in participants :
        (pDecision[p] = abort) =>
            (\E q \in participants : pVote[q] = no) \/
            (\E q \in participants : pAlive[q] = FALSE) \/
            (cAlive = FALSE)

(* AC4: Irrevocability – a participant's decision never changes once made *)
Irrevocability ==
    \A p \in participants :
        (pDecision[p] = commit => ALWAYS (pDecision[p] = commit)) /\
        (pDecision[p] = abort  => ALWAYS (pDecision[p] = abort))

(***************************************************************************)
(* The invariant required by the .cfg file                                 *)
(***************************************************************************)
Inv == ConsistentDecisions

=============================================================================