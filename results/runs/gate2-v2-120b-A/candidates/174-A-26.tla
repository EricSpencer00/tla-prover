---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants (to be supplied by the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS
    Node,               \* The set of node identifiers
    SlushLoopProcess,   \* One loop process per node
    SlushQueryProcess,  \* One query process per node
    HostMapping,        \* Set of triples [host |-> n, loop |-> p, query |-> q]
    SlushIterationCount,\* Max number of iterations each loop process performs
    SampleSetSize,      \* Number of peers sampled each round
    PickFlipThreshold,  \* Threshold of same-color replies needed to flip
    NoColor,            \* Sentinel value meaning "uncolored"
    NoMessage           \* Sentinel value meaning "no message"

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Colors == {"Red", "Blue"}

MessageType == {"Query", "Reply", "Terminate"}

Message == [type : MessageType,
            src  : SlushLoopProcess \cup SlushQueryProcess,
            dst  : SlushLoopProcess \cup SlushQueryProcess,
            color : Colors \cup {NoColor}]

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    colors,         \* [n \in Node |-> Colors \cup {NoColor}]
    msgs,           \* Set of in‑flight messages
    pc,             \* Program counters: [proc -> Nat] (see definitions below)
    sampleSet,      \* [p \in SlushLoopProcess |-> SUBSET Node]
    iterCount       \* [p \in SlushLoopProcess |-> Nat]

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
\* Mapping from a loop or query process to its host node
HostOf(p) ==
    IF p \in SlushLoopProcess THEN
        { hm.host : hm \in HostMapping : hm.loop = p }[1]
    ELSE
        { hm.host : hm \in HostMapping : hm.query = p }[1]

\* All process identifiers (loop + query)
AllProcs == SlushLoopProcess \cup SlushQueryProcess

\* The set of nodes whose loops have already sent a Terminate message
TerminatedLoops == { p \in SlushLoopProcess :
                     Len({ m \in msgs : m.type = "Terminate" /\ m.src = p }) > 0 }

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
    /\ colors   = [n \in Node |-> NoColor]
    /\ msgs     = {}
    /\ pc       = [proc \in AllProcs |-> 0]
    /\ sampleSet= [p \in SlushLoopProcess |-> {}]
    /\ iterCount= [p \in SlushLoopProcess |-> 0]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)

\* 1. Client assigns a color to an uncolored node
ClientAssign ==
    \E n \in Node :
        /\ colors[n] = NoColor
        /\ \E c \in Colors :
            /\ colors' = [colors EXCEPT ![n] = c]
            /\ UNCHANGED << msgs, pc, sampleSet, iterCount >>

\* 2. Loop process waits until its host node is colored
LoopRequireColor(p) ==
    /\ pc[p] = 0
    /\ colors[HostOf(p)] # NoColor
    /\ pc' = [pc EXCEPT ![p] = 1]
    /\ UNCHANGED << colors, msgs, sampleSet, iterCount >>

\* 3. Loop process selects a sample set and sends Query messages
LoopQuery(p) ==
    /\ pc[p] = 1
    /\ iterCount[p] < SlushIterationCount
    /\ \E subset \in SUBSET (Node \ {HostOf(p)}) :
        /\ Cardinality(subset) = SampleSetSize
        /\ sampleSet' = [sampleSet EXCEPT ![p] = subset]
        /\ msgs' = msgs \cup
            { [type |-> "Query",
               src  |-> p,
               dst  |-> HostMapping[? hm \in HostMapping :
                                      hm.host = n /\ hm.query = q][1],
               color|-> colors[HostOf(p)]] :
               n \in subset,
               \E q \in SlushQueryProcess :
                   HostMapping[? hm \in HostMapping :
                               hm.host = n /\ hm.query = q][1] = q }
        /\ pc' = [pc EXCEPT ![p] = 2]
        /\ UNCHANGED << colors, iterCount >>

\* 4. Query process receives a Query and replies (adopting color if uncolored)
QueryRespond(q) ==
    /\ pc[q] = 0
    /\ \E m \in msgs :
        /\ m.type = "Query"
        /\ m.dst = q
        /\ LET n == HostOf(q) IN
           /\ IF colors[n] = NoColor THEN
                  colors' = [colors EXCEPT ![n] = m.color]
              ELSE
                  colors' = colors
           /\ msgs' = msgs \ {m} \cup
                { [type  |-> "Reply",
                   src   |-> q,
                   dst   |-> m.src,
                   color |-> colors'[n]] }
           /\ pc' = [pc EXCEPT ![q] = 1]
           /\ UNCHANGED << sampleSet, iterCount >>

\* 5. Loop process tallies replies and possibly flips its node's color
LoopTally(p) ==
    /\ pc[p] = 2
    /\ \A n \in sampleSet[p] :
          \E r \in msgs :
              /\ r.type = "Reply"
              /\ r.dst = p
              /\ r.src = HostMapping[? hm \in HostMapping :
                                        hm.host = n /\ hm.query = q][1]
    /\ LET replies == { r.color : r \in msgs : r.type = "Reply" /\ r.dst = p } IN
       LET redCount  == Cardinality({c \in replies : c = "Red"}) IN
       LET blueCount == Cardinality({c \in replies : c = "Blue"}) IN
       LET majorityColor ==
            IF redCount >= PickFlipThreshold THEN "Red"
            ELSE IF blueCount >= PickFlipThreshold THEN "Blue"
            ELSE NoColor IN
       /\ colors' = IF majorityColor # NoColor
                      THEN [colors EXCEPT ![HostOf(p)] = majorityColor]
                      ELSE colors
       /\ msgs' = msgs \ { m \in msgs :
                           m.type = "Reply" /\ m.dst = p }
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
       /\ iterCount' = [iterCount EXCEPT ![p] = iterCount[p] + 1]
       /\ pc' = [pc EXCEPT ![p] = IF iterCount[p] + 1 = SlushIterationCount THEN 3 ELSE 1]

\* 6. Loop termination: broadcast a Terminate message
LoopTerminate(p) ==
    /\ pc[p] = 3
    /\ msgs' = msgs \cup
        { [type |-> "Terminate",
           src  |-> p,
           dst  |-> q,
           color|-> NoColor] :
           q \in SlushQueryProcess }
    /\ pc' = [pc EXCEPT ![p] = 4]
    /\ UNCHANGED << colors, sampleSet, iterCount >>

\* 7. Query processes exit when all loops have terminated
QueryExit(q) ==
    /\ pc[q] = 1
    /\ \A p \in SlushLoopProcess :
          \E m \in msgs :
              m.type = "Terminate" /\ m.dst = q /\ m.src = p
    /\ pc' = [pc EXCEPT ![q] = 2]
    /\ UNCHANGED << colors, msgs, sampleSet, iterCount >>

\* 8. Stuttering step to avoid deadlock
Stutter ==
    UNCHANGED << colors, msgs, pc, sampleSet, iterCount >>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in SlushLoopProcess : LoopRequireColor(p)
    \/ \E p \in SlushLoopProcess : LoopQuery(p)
    \/ \E q \in SlushQueryProcess : QueryRespond(q)
    \/ \E p \in SlushLoopProcess : LoopTally(p)
    \/ \E p \in SlushLoopProcess : LoopTerminate(p)
    \/ \E q \in SlushQueryProcess : QueryExit(q)
    \/ ClientAssign
    \/ Stutter

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<colors, msgs, pc, sampleSet, iterCount>>

(*-----------------------------------------------------------------
  Type invariant (the required INVARIANT)
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ colors \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message
    /\ pc \in [AllProcs -> Nat]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ iterCount \in [SlushLoopProcess -> Nat]
    /\ \A m \in msgs :
          /\ m.type \in MessageType
          /\ m.src \in AllProcs
          /\ m.dst \in AllProcs
          /\ m.color \in (Colors \cup {NoColor})

=============================================================================