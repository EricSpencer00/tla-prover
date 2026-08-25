---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

(* --------------------------------------------------------------------- *)
(* Two possible colors for the consensus *)
Colors == {"Red", "Blue"}

(* Process identifiers (loop, query, and a client placeholder) *)
ProcessId == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

(* Message record definition *)
Message == [type  : {"query", "reply", "term"},
            src   : ProcessId,
            dst   : ProcessId,
            color : (Colors \cup {NoColor})]

(* --------------------------------------------------------------------- *)
(* Helper functions to obtain host relationships from HostMapping *)
HostNodeOfLoop(lp) ==
  CHOOSE n \in Node :
    <<n, lp, q>> \in HostMapping /\ q \in SlushQueryProcess

HostQueryOfNode(n) ==
  CHOOSE q \in SlushQueryProcess :
    <<n, l, q>> \in HostMapping /\ l \in SlushLoopProcess

(* --------------------------------------------------------------------- *)
(* State variables *)
VARIABLES colors, msgs, sample, iter, doneLoop, doneQuery

(* --------------------------------------------------------------------- *)
(* Initial state *)
Init ==
  /\ colors   = [n \in Node |-> NoColor]
  /\ msgs     = {}
  /\ sample   = [lp \in SlushLoopProcess |-> {}]
  /\ iter     = [lp \in SlushLoopProcess |-> 0]
  /\ doneLoop = {}
  /\ doneQuery = {}

(* --------------------------------------------------------------------- *)
(* Client assigns a random color to an uncolored node *)
ClientAssign ==
  \E n \in Node :
    /\ colors[n] = NoColor
    /\ col \in Colors
    /\ colors' = [colors EXCEPT ![n] = col]
    /\ UNCHANGED <<msgs, sample, iter, doneLoop, doneQuery>>

(* --------------------------------------------------------------------- *)
(* Loop process selects a sample set and sends query messages *)
LoopSample(lp) ==
  /\ lp \in SlushLoopProcess
  /\ iter[lp] < SlushIterationCount
  /\ sample[lp] = {}
  /\ \E sampleSet \in SUBSET (Node \ { HostNodeOfLoop(lp) }) :
        /\ Cardinality(sampleSet) = SampleSetSize
        /\ sample' = [sample EXCEPT ![lp] = sampleSet]
        /\ msgs' = msgs \cup
                   { [type  |-> "query",
                      src   |-> lp,
                      dst   |-> HostQueryOfNode(n),
                      color |-> colors[HostNodeOfLoop(lp)] ] :
                     n \in sampleSet }
  /\ UNCHANGED <<colors, iter, doneLoop, doneQuery>>

(* --------------------------------------------------------------------- *)
(* Query process replies to a query (and may adopt the query's color) *)
QueryRespond ==
  \E m \in msgs :
    /\ m.type = "query"
    /\ qp == m.dst
    /\ qp \in SlushQueryProcess
    /\ LET n == CHOOSE node \in Node : HostQueryOfNode(node) = qp IN
         IF colors[n] = NoColor
            THEN colors' = [colors EXCEPT ![n] = m.color]
            ELSE colors' = colors
    /\ LET reply ==
            [type  |-> "reply",
             src   |-> qp,
             dst   |-> m.src,
             color |-> colors'[n]]
       IN msgs' = (msgs \ {m}) \cup {reply}
    /\ UNCHANGED <<sample, iter, doneLoop, doneQuery>>

(* --------------------------------------------------------------------- *)
(* Loop process tallies replies and possibly flips its color *)
TallyReplies(lp) ==
  /\ lp \in SlushLoopProcess
  /\ iter[lp] < SlushIterationCount
  /\ sample[lp] # {}
  /\ replies == { m \in msgs :
                    m.type = "reply" /\ m.dst = lp /\
                    m.src \in { HostQueryOfNode(n) : n \in sample[lp] } }
  /\ Cardinality(replies) = SampleSetSize
  /\ reds  == Cardinality({ r \in replies : r.color = "Red" })
  /\ blues == Cardinality({ r \in replies : r.color = "Blue" })
  /\ newColor ==
        IF reds  >= PickFlipThreshold THEN "Red"
        ELSE IF blues >= PickFlipThreshold THEN "Blue"
        ELSE colors[HostNodeOfLoop(lp)]
  /\ colors' = [colors EXCEPT ![HostNodeOfLoop(lp)] = newColor]
  /\ sample' = [sample EXCEPT ![lp] = {}]
  /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
  /\ msgs'   = msgs \ replies
  /\ UNCHANGED <<doneLoop, doneQuery>>

(* --------------------------------------------------------------------- *)
(* Loop process terminates after completing the prescribed iterations *)
LoopTerminate(lp) ==
  /\ lp \in SlushLoopProcess
  /\ iter[lp] = SlushIterationCount
  /\ doneLoop' = doneLoop \cup {lp}
  /\ LET termMsgs ==
        { [type  |-> "term",
           src   |-> lp,
           dst   |-> qp,
           color |-> NoColor] :
           qp \in SlushQueryProcess }
     IN msgs' = msgs \cup termMsgs
  /\ UNCHANGED <<colors, sample, iter>>

(* --------------------------------------------------------------------- *)
(* Query process exits after receiving termination from all loop processes *)
QueryTerminate ==
  \E qp \in SlushQueryProcess :
    /\ { m \in msgs : m.type = "term" /\ m.dst = qp } =
       { [type |-> "term",
          src  |-> lp,
          dst  |-> qp,
          color|-> NoColor] :
          lp \in SlushLoopProcess }
    /\ doneQuery' = doneQuery \cup {qp}
    /\ msgs' = msgs \ { m \in msgs : m.type = "term" /\ m.dst = qp }
    /\ UNCHANGED <<colors, sample, iter, doneLoop>>

(* --------------------------------------------------------------------- *)
(* Overall next-state relation *)
Next ==
  \/ ClientAssign
  \/ \E lp \in SlushLoopProcess : LoopSample(lp)
  \/ \E lp \in SlushLoopProcess : TallyReplies(lp)
  \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
  \/ QueryRespond
  \/ QueryTerminate

(* --------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<colors, msgs, sample, iter, doneLoop, doneQuery>>

(* --------------------------------------------------------------------- *)
(* Type invariant *)
TypeInvariant ==
  /\ colors   \in [Node -> (Colors \cup {NoColor})]
  /\ msgs     \subseteq Message
  /\ sample   \in [SlushLoopProcess -> SUBSET Node]
  /\ iter     \in [SlushLoopProcess -> Nat]
  /\ doneLoop \subseteq SlushLoopProcess
  /\ doneQuery \subseteq SlushQueryProcess

====