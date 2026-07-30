---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Natural-language specification: the Slush protocol from the Avalanche  *)
(* whitepaper.  This is an executable PlusCal model, so the concurrent      *)
(* actions below are written as atomic steps against a shared message set.   *)

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

ASSUME Cardinality(Node) = Cardinality(SlushLoopProcess)
ASSUME Cardinality(Node) = Cardinality(SlushQueryProcess)

RECURSIVE Count(_, _)
Count(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Count(f, S \ {x})

VARIABLES
  color, msgs, pc, sampleSet, loopIter

vars == <<color, msgs, pc, sampleSet, loopIter>>

TypeOK ==
  /\ color \in [Node -> {NoColor} \union {"red", "blue"}]
  /\ msgs \subseteq ({SlushLoopProcess \union SlushQueryProcess \union {"terminator"}} \times (Node \union {"red", "blue", NoMessage}))
  /\ pc \in [SlushLoopProcess \union SlushQueryProcess \union {"client"} -> 0..3]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
  /\ loopIter \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \union SlushQueryProcess \union {"client"} |-> 0]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ loopIter = [lp \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node; this is the only
\* way a node's color becomes non-empty without a Slush round voting.
AssignColor ==
  /\ \E n \in Node, col \in {"red", "blue"} :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = col]
  /\ UNCHANGED <<msgs, pc, sampleSet, loopIter>>

\* A loop process may only start sampling once its host node has been colored.
RequireColor ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = 0
       /\ \E n \in Node : <<lp, n>> \in HostMapping /\ color[n] # NoColor
       /\ pc' = [pc EXCEPT ![lp] = 1]
  /\ UNCHANGED <<color, msgs, sampleSet, loopIter>>

\* The loop process sends a query message to a random fixed-size sample of
\* peers, each query carrying the loop's current color.
QuerySampleSet ==
  /\ \E lp \in SlushLoopProcess, peers \in SUBSET Node :
       /\ pc[lp] = 1
       /\ Cardinality(peers) = SampleSetSize
       /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
       /\ msgs' = msgs \union {[lp |-> p, "red"] : p \in peers}
                     \union {[lp |-> p, "blue"] : p \in peers}
       /\ pc' = [pc EXCEPT ![lp] = 2]
  /\ UNCHANGED <<color, loopIter>>

\* A query process receives a query, adopts the query's color if uncolored,
\* and replies with its current color.
RespondToQuery ==
  /\ \E qp \in SlushQueryProcess, lp \in SlushLoopProcess, col \in {"red", "blue"} :
       /\ [lp |-> qp, col] \in msgs
       /\ msgs' = (msgs \ {[lp |-> qp, col]})
            \union {[qp |-> lp, IF color[qp] = NoColor THEN col ELSE color[qp]]}
       /\ color' = IF color[qp] = NoColor
                   THEN [color EXCEPT ![qp] = col]
                   ELSE color
  /\ UNCHANGED <<pc, sampleSet, loopIter>>

\* Having collected every reply, the loop adopts a color that reaches the
\* flip threshold and advances one iteration.
TallyReplies ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = 2
       /\ \A n \in sampleSet[lp] : [qp |-> n, "red"] \in msgs \/ [qp |-> n, "blue"] \in msgs
       /\ LET reds == Count([n \in sampleSet[lp] |-> IF [qp |-> n, "red"] \in msgs THEN 1 ELSE 0], sampleSet[lp])
              blues == Count([n \in sampleSet[lp] |-> IF [qp |-> n, "blue"] \in msgs THEN 1 ELSE 0], sampleSet[lp])
          IN color' = [color EXCEPT ![lp] = IF reds >= PickFlipThreshold THEN "red"
                                          ELSE IF blues >= PickFlipThreshold THEN "blue"
                                          ELSE color[lp]]
       /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
       /\ loopIter' = [loopIter EXCEPT ![lp] = IF @ < SlushIterationCount THEN @ + 1 ELSE @]
       /\ pc' = [pc EXCEPT ![lp] = 2]
  /\ UNCHANGED msgs

\* After finishing all iterations, the loop process broadcasts a terminator.
LoopTermination ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = 2
       /\ loopIter[lp] = SlushIterationCount
       /\ [lp |-> "terminator"] \notin msgs
       /\ msgs' = msgs \union {[lp |-> "terminator"]}
       /\ pc' = [pc EXCEPT ![lp] = 3]
  /\ UNCHANGED <<color, sampleSet, loopIter>>

\* Query processes drop out once every loop process has sent a terminator.
QueryExit ==
  /\ \E qp \in SlushQueryProcess :
       /\ pc[qp] = 0
       /\ \A lp \in SlushLoopProcess : [lp |-> "terminator"] \in msgs
       /\ pc' = [pc EXCEPT ![qp] = 3]
  /\ UNCHANGED <<color, msgs, sampleSet, loopIter>>

Next ==
  \/ AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
  \/ TallyReplies \/ LoopTermination \/ QueryExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(AssignColor) /\ WF_vars(QuerySampleSet)
        /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)

TypeInvariant == TypeOK

\* Every process eventually reaches its done state.
Termination == <>(\A p \in SlushLoopProcess \union SlushQueryProcess \union {"client"} : pc[p] = 3)

====