---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Node,                     \* set of node identifiers
  SlushLoopProcess,         \* set of loop process identifiers
  SlushQueryProcess,        \* set of query process identifiers
  HostMapping,              \* set of triples <<node, loopProc, queryProc>>
  SlushIterationCount,      \* number of iterations each loop runs
  SampleSetSize,            \* size of the peer sample per round
  PickFlipThreshold,        \* threshold to adopt a color
  NoColor,                  \* special value meaning “uncolored”
  NoMessage                 \* special value meaning “no message”

(* ----------------------------------------------------------------------
   Auxiliary definitions
   ---------------------------------------------------------------------- *)

Colors == {"Red", "Blue"}                     \* the two possible colors

Message == 
  [type : {"query", "reply", "term"},
   src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}),
   dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}),
   col  : (Colors \cup {NoColor})]

VARIABLES
  color,   \* [node \in Node |-> Colors \cup {NoColor}]
  msgs,    \* set of messages in flight
  sample,  \* [lp \in SlushLoopProcess |-> SUBSET Node]  (current sample)
  iter,    \* [lp \in SlushLoopProcess |-> Nat]          (iterations done)
  pc       \* [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> String]

(* ----------------------------------------------------------------------
   Helper functions that read the host mapping
   ---------------------------------------------------------------------- *)

HostNode(p) ==
  CHOOSE n \in Node : <<n, p, _>> \in HostMapping

HostNodeOfQuery(q) ==
  CHOOSE n \in Node : <<n, _, q>> \in HostMapping

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs   = {}
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ iter   = [lp \in SlushLoopProcess |-> 0]
  /\ pc     = [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> "Ready"]

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* 1. Client assigns a random color to an uncolored node *)
ClientAssign ==
  /\ \E n \in Node : color[n] = NoColor
  /\ \E col \in Colors :
       LET n == CHOOSE n \in Node : color[n] = NoColor IN
         /\ color' = [color EXCEPT ![n] = col]
         /\ UNCHANGED <<msgs, sample, iter, pc>>
  /\ pc' = [pc EXCEPT !["Client"] = "Ready"]

(* 2. Loop process waits until its host node is colored *)
LoopRequireColor(lp) ==
  /\ lp \in SlushLoopProcess
  /\ LET n == HostNode(lp) IN color[n] # NoColor
  /\ pc' = [pc EXCEPT ![lp] = "Iterating"]
  /\ UNCHANGED <<color, msgs, sample, iter>>

(* 3. Loop process samples peers and sends query messages *)
LoopSample(lp) ==
  /\ lp \in SlushLoopProcess
  /\ pc[lp] = "Iterating"
  /\ LET n == HostNode(lp) IN
     LET curCol == color[n] IN
     \E s \subseteq Node \ {n} :
        /\ Cardinality(s) = SampleSetSize
        /\ sample' = [sample EXCEPT ![lp] = s]
        /\ msgs' = msgs \cup
           { [type |-> "query",
              src  |-> lp,
              dst  |-> q,
              col  |-> curCol] :
               q \in SlushQueryProcess :
               LET node_q == HostNodeOfQuery(q) IN node_q \in s }
        /\ pc' = [pc EXCEPT ![lp] = "WaitingReplies"]
        /\ UNCHANGED <<color, iter>>

(* 4. Query process receives a query, possibly adopts the color, and replies *)
QueryReceive(q) ==
  /\ q \in SlushQueryProcess
  /\ \E m \in msgs :
        m.type = "query" /\ m.dst = q
  /\ LET m == CHOOSE m \in msgs :
        m.type = "query" /\ m.dst = q IN
     LET n == HostNodeOfQuery(q) IN
     LET newCol ==
        IF color[n] = NoColor THEN m.col ELSE color[n] IN
     /\ color' = [color EXCEPT ![n] = newCol]
     /\ msgs' = (msgs \ {m}) \cup
        { [type |-> "reply",
           src  |-> q,
           dst  |-> m.src,
           col  |-> newCol] }
     /\ pc' = [pc EXCEPT ![q] = "ReplySent"]
     /\ UNCHANGED <<sample, iter>>

(* 5. Loop process tallies replies and possibly flips its color *)
LoopTally(lp) ==
  /\ lp \in SlushLoopProcess
  /\ pc[lp] = "WaitingReplies"
  /\ LET n == HostNode(lp) IN
     LET s == sample[lp] IN
     (* all replies from the sampled peers must be present *)
     \A q \in SlushQueryProcess :
        (LET node_q == HostNodeOfQuery(q) IN node_q \in s) =>
        \E r \in msgs :
           r.type = "reply" /\ r.dst = lp /\ r.src = q
  /\ LET reds  == { r \in msgs :
                       r.type = "reply" /\ r.dst = lp /\ r.col = "Red" } IN
     blues == { r \in msgs :
                       r.type = "reply" /\ r.dst = lp /\ r.col = "Blue" } IN
     redCnt  == Cardinality(reds) IN
     blueCnt == Cardinality(blues) IN
     newCol ==
        IF redCnt >= PickFlipThreshold THEN "Red"
        ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
        ELSE color[n] IN
     /\ color' = [color EXCEPT ![n] = newCol]
     /\ msgs' = msgs \ 
        { r \in msgs :
            r.type = "reply" /\ r.dst = lp /\ r.src \in
               { q \in SlushQueryProcess :
                     LET node_q == HostNodeOfQuery(q) IN node_q \in s } }
     /\ sample' = [sample EXCEPT ![lp] = {}]
     /\ iter'   = [iter EXCEPT ![lp] = iter[lp] + 1]
     /\ pc' =
        IF iter'[lp] = SlushIterationCount
           THEN [pc EXCEPT ![lp] = "Terminating"]
           ELSE [pc EXCEPT ![lp] = "Iterating"]
     /\ UNCHANGED <<>>

(* 6. Loop process broadcasts termination *)
LoopTerminate(lp) ==
  /\ lp \in SlushLoopProcess
  /\ pc[lp] = "Terminating"
  /\ msgs' = msgs \cup
        { [type |-> "term",
           src  |-> lp,
           dst  |-> "all",
           col  |-> NoColor] }
  /\ pc' = [pc EXCEPT ![lp] = "Done"]
  /\ UNCHANGED <<color, sample, iter>>

(* 7. Query processes exit when termination messages from all loops have been seen *)
QueryExit(q) ==
  /\ q \in SlushQueryProcess
  /\ pc[q] # "Done"
  /\ \A lp \in SlushLoopProcess :
        \E m \in msgs : m.type = "term" /\ m.src = lp
  /\ pc' = [pc EXCEPT ![q] = "Done"]
  /\ UNCHANGED <<color, msgs, sample, iter>>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)

Next ==
  \/ \E lp \in SlushLoopProcess : LoopRequireColor(lp)
  \/ \E lp \in SlushLoopProcess : LoopSample(lp)
  \/ \E q \in SlushQueryProcess : QueryReceive(q)
  \/ \E lp \in SlushLoopProcess : LoopTally(lp)
  \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
  \/ \E q \in SlushQueryProcess : QueryExit(q)
  \/ ClientAssign

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)

TypeInvariant ==
  /\ color \in [Node -> (Colors \cup {NoColor})]
  /\ msgs \subseteq Message

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<color, msgs, sample, iter, pc>>

====