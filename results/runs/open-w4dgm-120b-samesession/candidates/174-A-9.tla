---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush is the simplest member of the Snow family of probabilistic consensus    *)
(* protocols.  Each node (actor) has a loop process that samples random peers   *)
(* and a query process that answers sampled queries.  The spec models the       *)
(* message exchange as two-way communication between the loop and query         *)
(* processes; loop processes tally replies and flip their node's color when a   *)
(* sampled majority is reached.  The host mapping links each node with its      *)
(* loop and query processes.                                                    *)

(* In TLA+ there is no probabilistic choice, so Slush is modeled here as       *)
(* ordinary nondeterministic choice over the uniformly-distributed sampling     *)
(* of peers -- this is the executable pseudocode, not a stochastic model.       *)

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

Message == [kind: {"query", "reply", "done"}, pair: SlushLoopProcess \X SlushQueryProcess, paint: {NoColor} \union {1, 2}]
ReplyCount == {"uncolored", "colorOne", "colorTwo"}

VARIABLES paint, inbox, pc, sample, replied

vars == <<paint, inbox, pc, sample, replied>>

TypeOK ==
    /\ paint \in [Node -> {NoColor} \union {1, 2}]
    /\ inbox \subseteq Message
    /\ pc \in [SlushLoopProcess \union SlushQueryProcess -> {"idle", "active", "done"}]
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ replied \in [SlushLoopProcess -> ReplyCount]

Init ==
    /\ paint = [n \in Node |-> NoColor]
    /\ inbox = {}
    /\ pc = [p \in (SlushLoopProcess \union SlushQueryProcess) |-> "idle"]
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ replied = [p \in SlushLoopProcess |-> "uncolored"]

\* A client request assigns an initial color to an uncolored node.
ClientAssignColor ==
    \E n \in Node, c \in {1, 2} :
        /\ paint[n] = NoColor
        /\ paint' = [paint EXCEPT ![n] = c]
        /\ UNCHANGED <<inbox, pc, sample, replied>>

\* Loop processes wait for their host node to be colored before iterating.
RequireColor ==
    \E p \in SlushLoopProcess :
        /\ pc[p] = "idle"
        /\ LET n == CHOOSE n \in Node : <<n, p, NoMessage>> \in HostMapping
           IN paint[n] # NoColor
        /\ pc' = [pc EXCEPT ![p] = "active"]
        /\ UNCHANGED <<paint, inbox, sample, replied>>

\* The loop process queries a random sample of distinct peers, sending each a
\* message that carries the loop's own current color.
QuerySampleSet ==
    \E p \in SlushLoopProcess :
        /\ pc[p] = "active"
        /\ sample[p] = {}
        /\ \E peers \in SUBSET SlushQueryProcess :
             /\ Cardinality(peers) = SampleSetSize
             /\ LET n == CHOOSE n \in Node : <<n, p, NoMessage>> \in HostMapping
                IN \A q \in peers :
                     LET m == CHOOSE m \in Node : <<m, NoMessage, q>> \in HostMapping
                         kind == IF paint[n] = NoColor THEN "uncolored" ELSE "query"
                     IN inbox' = inbox \union {[kind |-> kind, pair |-> <<p, q>>, paint |-> paint[n]]}
             /\ sample' = [sample EXCEPT ![p] = peers]
        /\ UNCHANGED <<paint, pc, replied>>

\* Query processes answer queries; an uncolored node adopts the query's color.
RespondToQuery ==
    \E m \in inbox :
        /\ m.kind = "query"
        /\ LET q == m.pair[2] IN
           \E n \in Node :
               /\ <<n, NoMessage, q>> \in HostMapping
               /\ paint' = [paint EXCEPT ![n] = IF paint[n] = NoColor THEN m.paint ELSE paint[n]]
               /\ inbox' = (inbox \ {m}) \union {[kind |-> "reply", pair |-> m.pair, paint |-> paint[n]]}
        /\ UNCHANGED <<pc, sample, replied>>

\* Replies travel back to the loop process; it tallies them and flips if a
\* majority (the pick flip threshold) of the sampled peers agrees.
TallyReplies ==
    \E p \in SlushLoopProcess :
        /\ pc[p] = "active"
        /\ sample[p] # {}
        /\ \E m \in inbox :
             /\ m.kind = "reply"
             /\ m.pair[1] = p
             /\ replied' = [replied EXCEPT ![p] =
                  IF m.paint = NoColor THEN replied[p]
                  ELSE IF m.paint = 1 THEN [replied[p] EXCEPT !.colorOne = replied[p].colorOne + 1]
                  ELSE [replied[p] EXCEPT !.colorTwo = replied[p].colorTwo + 1]]
             /\ inbox' = inbox \ {m}
        /\ LET n == CHOOSE n \in Node : <<n, p, NoMessage>> \in HostMapping
               majorityOne == replied[p].colorOne >= PickFlipThreshold
               majorityTwo == replied[p].colorTwo >= PickFlipThreshold
           IN paint' = IF majorityOne \/ majorityTwo
                         THEN [paint EXCEPT ![n] = IF majorityOne THEN 1 ELSE 2]
                         ELSE paint
        /\ pc' = [pc EXCEPT ![p] = IF Cardinality(sample[p]) = SampleSetSize
                                     THEN "done" ELSE pc[p]]
        /\ sample' = [sample EXCEPT ![p] = IF Cardinality(sample[p]) = SampleSetSize
                                          THEN {} ELSE sample[p]]
        /\ replied' = [replied EXCEPT ![p] = IF Cardinality(sample[p]) = SampleSetSize
                                              THEN "uncolored" ELSE replied[p]]

\* A loop process that has exhausted its iterations broadcasts termination.
LoopTerminate ==
    \E p \in SlushLoopProcess :
        /\ pc[p] = "done"
        /\ replied[p] = "uncolored"
        /\ LET doneCount == Cardinality({q \in SlushLoopProcess : pc[q] = "done"})
           IN doneCount < SlushIterationCount
        /\ inbox' = inbox \union {[kind |-> "done", pair |-> <<p, NoMessage>>, paint |-> NoColor]}
        /\ UNCHANGED <<paint, pc, sample, replied>>

\* Query processes exit when every loop process has terminated.
QueryLoopExit ==
    /\ \A p \in SlushLoopProcess : pc[p] = "done"
    /\ \A q \in SlushQueryProcess : pc[q] # "active"
    /\ \E q \in SlushQueryProcess :
         pc' = [pc EXCEPT ![q] = "done"]
    /\ UNCHANGED <<paint, inbox, sample, replied>>

Next == ClientAssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
        /\ WF_vars(TallyReplies) /\ WF_vars(LoopTerminate) /\ WF_vars(QueryLoopExit)

(* Slush's only safety property is a type invariant on its shared variables.  *)
(* Convergence (which color wins) is probabilistic and not expressible in TLA+. *)
TypeInvariant == TypeOK

(* Every process eventually reaches its done state.                              *)
Termination == \A p \in (SlushLoopProcess \union SlushQueryProcess) : <>(pc[p] = "done")
====