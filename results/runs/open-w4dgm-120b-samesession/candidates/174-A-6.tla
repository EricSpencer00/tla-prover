---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush protocol: a metastable Snow-family consensus mechanism.  Loop      *)
(* processes repeatedly sample peer nodes and adopt a sufficiently popular   *)
(* color, causing the network to converge.  Node colors are drawn from a      *)
(* bounded range of two colors plus an uncolored state.  This PlusCal spec     *)
(* is written as faithful pseudocode; it is not meant to model the            *)
(* protocol's probabilistic convergence, only its control flow.               *)

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
           SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

(* The set of in-flight messages, each tagged by its sender, receiver,      *)
(* kind, and carried color payload.                                            *)
Messages == Node \X Node \X {"query", "queryReply", "terminates"} \X (1..2 \cup {NoColor})

VARIABLES color, message, pc, sampleSet, loopIteration

vars == <<color, message, pc, sampleSet, loopIteration>>

LoopType == [host: Node, pc: {"waitColor", "tallyReplies", "done"}]
ReplyType == [host: Node, pc: {"replying", "exited"}]

RECURSIVE Tally(_)
Tally(S) == IF S = {} THEN [c1 |-> 0, c2 |-> 0]
            ELSE LET e == CHOOSE e \in S : TRUE IN
                 LET rest == Tally(S \ {e}) IN
                 IF e = 1 THEN [c1 |-> rest.c1 + 1, c2 |-> rest.c2]
                 ELSE           [c1 |-> rest.c1, c2 |-> rest.c2 + 1]

TypeOK ==
    /\ color \in [Node -> (1..2) \cup {NoColor}]
    /\ message \subseteq Messages
    /\ pc \in [SlushLoopProcess -> LoopType] \union [SlushQueryProcess -> ReplyType]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ loopIteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ message = {}
    /\ pc = [lp \in SlushLoopProcess |-> [host |-> CHOOSE n \in Node : <<n, lp, NoMessage>> \in HostMapping,
                                          pc |-> "waitColor"]]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ loopIteration = [lp \in SlushLoopProcess |-> 0]

\* A client transaction assigns a random color to an uncolored node.
AssignColor(n) ==
    \E c \in {1, 2} :
        /\ color[n] = NoColor
        /\ color' = [color EXCEPT ![n] = c]
        /\ UNCHANGED <<message, pc, sampleSet, loopIteration>>

RequireColor(lp) ==
    /\ pc[lp].pc = "waitColor"
    /\ color[pc[lp].host] # NoColor
    /\ pc' = [pc EXCEPT ![lp].pc = "tallyReplies"]
    /\ UNCHANGED <<color, message, sampleSet, loopIteration>>

Query(lp) ==
    /\ pc[lp].pc = "tallyReplies"
    /\ sampleSet[lp] = {}
    /\ Cardinality(Node) - 1 >= SampleSetSize
    /\ \E peers \in SUBSET (Node \ {pc[lp].host}) :
        /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
        /\ message' = message \union
                      {<<pc[lp].host, q, "query", color[pc[lp].host]>> : q \in peers}
    /\ UNCHANGED <<color, pc, loopIteration>>

Respond(n, q) ==
    /\ <<n, q, "query", NoColor>> \in message
    /\ message' = (message \ {<<n, q, "query", NoColor>>})
                  \union {<<n, q, "queryReply", IF color[n] = NoColor THEN q ELSE color[n]>>}
    /\ color' = [color EXCEPT ![n] = IF color[n] = NoColor THEN q ELSE color[n]]
    /\ UNCHANGED <<pc, sampleSet, loopIteration>>

TallyReplies(lp) ==
    /\ pc[lp].pc = "tallyReplies"
    /\ sampleSet[lp] # {}
    /\ \A q \in sampleSet[lp] : <<q, pc[lp].host, "queryReply", NoColor>> \in message
    /\ LET replied == {<<q, pc[lp].host, "queryReply", NoColor>> : q \in sampleSet[lp]}
       IN
       LET tally == Tally({m[4] : m \in replied}) IN
       /\ IF tally.c1 >= PickFlipThreshold THEN color' = [color EXCEPT ![pc[lp].host] = 1]
          ELSE IF tally.c2 >= PickFlipThreshold THEN color' = [color EXCEPT ![pc[lp].host] = 2]
          ELSE color' = color
       /\ message' = message \replied
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
    /\ loopIteration' = [loopIteration EXCEPT ![lp] =
                            IF loopIteration[lp] < SlushIterationCount
                            THEN loopIteration[lp] + 1 ELSE loopIteration[lp]]
    /\ UNCHANGED pc

Terminate(lp) ==
    /\ pc[lp].pc = "tallyReplies"
    /\ loopIteration[lp] = SlushIterationCount
    /\ pc' = [pc EXCEPT ![lp].pc = "done"]
    /\ message' = message \union {<<pc[lp].host, pc[lp].host, "terminates", NoColor>>}
    /\ UNCHANGED <<color, sampleSet, loopIteration>>

ExitReply(q) ==
    /\ pc[q].pc = "replying"
    /\ \A lp \in SlushLoopProcess : <<pc[lp].host, pc[q].host, "terminates", NoColor>> \in message
    /\ pc' = [pc EXCEPT ![q].pc = "exited"]
    /\ UNCHANGED <<color, message, sampleSet, loopIteration>>

RespondStep == \E n \in Node, q \in Node : Respond(n, q)
TerminateStep == \E lp \in SlushLoopProcess : Terminate(lp)

Next ==
    \/ \E n \in Node : AssignColor(n)
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess : Query(lp)
    \/ RespondStep
    \/ \E lp \in SlushLoopProcess : TallyReplies(lp)
    \/ TerminateStep
    \/ \E q \in SlushQueryProcess : ExitReply(q)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(RespondStep) /\ WF_vars(TerminateStep)

TypeInvariant == TypeOK

(* Every process eventually reaches its done state.  Convergence of all    *)
(* nodes to a single color is a probabilistic guarantee and is not checked  *)
(* by this model; only process termination is verified here.                *)
Termination == (\A lp \in SlushLoopProcess : pc[lp].pc = "done") /\ (\A q \in SlushQueryProcess : pc[q].pc = "exited")

====