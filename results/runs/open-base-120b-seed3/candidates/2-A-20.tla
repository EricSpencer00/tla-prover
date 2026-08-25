---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* ---------------------------------------------------------------------- *)
(* Types *)
Vote      == { yes , no }
Decision  == { undecided , commit , abort }
FwdStatus == { notsent , commit , abort }

(* ---------------------------------------------------------------------- *)
(* Variables *)
VARIABLES
    coordAlive,      \* Is the coordinator up?
    coordFaulty,     \* Has the coordinator crashed?
    coordState,      \* Coordinator internal state (only waiting is used)
    coordDecision,   \* Decision made by the coordinator (undecided/commit/abort)

    alive,           \* Mapping participants -> BOOLEAN (TRUE = up)
    faulty,          \* Mapping participants -> BOOLEAN (TRUE = crashed)
    vote,            \* Mapping participants -> Vote
    voteSent,        \* Mapping participants -> BOOLEAN (TRUE = vote sent)
    preDec,          \* Mapping participants -> Decision (pre‑decision)
    decision,        \* Mapping participants -> Decision (final decision)
    fwd               \* Forwarding table: [p][q] = FwdStatus

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)
Participant == participants

Alive(p)   == alive[p]
Faulty(p)  == faulty[p]

AllAlive   == \A p \in participants : Alive(p)
AllFaulty  == \A p \in participants : Faulty(p)

Vars == <<
          coordAlive , coordFaulty , coordState , coordDecision ,
          alive , faulty , vote , voteSent , preDec , decision , fwd
       >>

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ coordAlive   = TRUE
    /\ coordFaulty  = FALSE
    /\ coordState   = waiting
    /\ coordDecision= undecided

    /\ alive        = [p \in participants |-> TRUE]
    /\ faulty       = [p \in participants |-> FALSE]

    /\ vote         = [p \in participants |-> no]          \* placeholder
    /\ voteSent     = [p \in participants |-> FALSE]

    /\ preDec       = [p \in participants |-> undecided]
    /\ decision     = [p \in participants |-> undecided]

    /\ fwd          = [p \in participants |-> [q \in participants |-> notsent]]

(* ---------------------------------------------------------------------- *)
(* Coordinator actions *)

CoordDecide ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : voteSent[p]               \* all votes received
    /\ IF \A p \in participants : vote[p] = yes
          THEN coordDecision' = commit
          ELSE coordDecision' = abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordState,
                    alive, faulty, vote, voteSent,
                    preDec, decision, fwd>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive'  = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordState, coordDecision,
                    alive, faulty, vote, voteSent,
                    preDec, decision, fwd>>

(* ---------------------------------------------------------------------- *)
(* Participant actions, parameterized by a participant p *)

SendVote(p) ==
    /\ Alive(p)
    /\ ~voteSent[p]
    /\ \E v \in Vote :
          /\ vote'   = [vote   EXCEPT ![p] = v]
          /\ voteSent'= [voteSent EXCEPT ![p] = TRUE]
          /\ UNCHANGED <<coordAlive, coordFaulty, coordState, coordDecision,
                        alive, faulty, preDec, decision, fwd>>

PreDecFromCoord(p) ==
    /\ Alive(p)
    /\ preDec[p] = undecided
    /\ coordDecision # undecided
    /\ preDec' = [preDec EXCEPT ![p] = coordDecision]
    /\ fwd'    = [fwd EXCEPT ![p][p] = coordDecision]   \* store at own entry
    /\ UNCHANGED <<coordAlive, coordFaulty, coordState, coordDecision,
                  alive, faulty, vote, voteSent, decision>>

PreDecFromForward(p) ==
    /\ Alive(p)
    /\ preDec[p] = undecided
    /\ \E q \in participants :
          /\ q # p
          /\ fwd[q][p] # notsent
          /\ LET d == IF fwd[q][p] = commit THEN commit ELSE abort IN
               /\ preDec' = [preDec EXCEPT ![p] = d]
               /\ fwd'    = [fwd EXCEPT ![p][p] = d]
               /\ UNCHANGED <<coordAlive, coordFaulty, coordState, coordDecision,
                             alive, faulty, vote, voteSent, decision>>
         

Forward(p) ==
    /\ Alive(p)
    /\ preDec[p] # undecided
    /\ \E q \in participants :
          /\ q # p
          /\ fwd[p][q] = notsent
          /\ LET d == preDec[p] IN
               /\ fwd' = [fwd EXCEPT ![p][q] = d]
               /\ UNCHANGED <<coordAlive, coordFaulty, coordState, coordDecision,
                             alive, faulty, vote, voteSent, preDec, decision>>

Decide(p) ==
    /\ Alive(p)
    /\ preDec[p] # undecided
    /\ \A q \in participants : fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = preDec[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordState, coordDecision,
                  alive, faulty, vote, voteSent, preDec, fwd>>

AbortTimeout(p) ==
    /\ Alive(p)
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in participants :
          (Alive(q) => fwd[q][q] = notsent)                     \* no alive participant has a pre‑decision
    /\ \A q \in participants :
          (~Alive(q) => \A r \in participants :
                           (Alive(r) => fwd[q][r] = notsent))   \* dead participants have not forwarded anything
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordState, coordDecision,
                  alive, faulty, vote, voteSent, preDec, fwd>>

Die(p) ==
    /\ Alive(p)
    /\ alive'  = [alive  EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordState, coordDecision,
                  vote, voteSent, preDec, decision, fwd>>

(* ---------------------------------------------------------------------- *)
(* Combined next-state relation *)

Next ==
    \/ CoordDecide
    \/ CoordDie
    \/ \E p \in participants :
          \/ SendVote(p)
          \/ PreDecFromCoord(p)
          \/ PreDecFromForward(p)
          \/ Forward(p)
          \/ Decide(p)
          \/ AbortTimeout(p)
          \/ Die(p)

(* ---------------------------------------------------------------------- *)
(* Specification *)

SpecNB == Init /\ [][Next]_Vars

(* ---------------------------------------------------------------------- *)
(* Type invariants *)

TypeInvNB ==
    /\ coordAlive   \in BOOLEAN
    /\ coordFaulty  \in BOOLEAN
    /\ coordState   \in { waiting }
    /\ coordDecision \in Decision

    /\ alive        \in [participants -> BOOLEAN]
    /\ faulty       \in [participants -> BOOLEAN]

    /\ vote         \in [participants -> Vote]
    /\ voteSent     \in [participants -> BOOLEAN]

    /\ preDec       \in [participants -> Decision]
    /\ decision     \in [participants -> Decision]

    /\ fwd          \in [participants -> [participants -> FwdStatus]]

=============================================================================