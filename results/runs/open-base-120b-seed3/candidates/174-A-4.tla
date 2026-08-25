---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Node,                     \* set of all node identifiers
  SlushLoopProcess,         \* one loop process per node
  SlushQueryProcess,        \* one query process per node
  HostMapping,              \* set of triples <<node, loopProc, queryProc>>
  SlushIterationCount,      \* number of iterations each loop performs
  SampleSetSize,            \* size of the peer sample each round
  PickFlipThreshold,        \* threshold for adopting a color
  NoColor,                  \* sentinel for “uncolored”
  NoMessage                 \* sentinel for “no message”

\* ----------------------------------------------------------------------
\* Derived sets and record types
Proc == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

Colors == {"Red", "Blue"}

Message == [type  : {"query", "reply", "term"},
            src   : Proc,
            dst   : Proc,
            color : (Colors \cup {NoColor, NoMessage})]

\* ----------------------------------------------------------------------
\* Helper functions to extract the mapping from HostMapping
NodeOfLoop(lp) ==
  CHOOSE n \in Node : <<n, lp, _>> \in HostMapping

LoopOfNode(n) ==
  CHOOSE lp \in SlushLoopProcess : <<n, lp, _>> \in HostMapping

QueryOfNode(n) ==
  CHOOSE qp \in SlushQueryProcess : <<n, _, qp>> \in HostMapping

NodeOfQuery(qp) ==
  CHOOSE n \in Node : <<n, _, qp>> \in HostMapping

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
  Color,   \* [node -> color]  (color or NoColor)
  Msgs,    \* set of in‑flight messages
  PC,      \* program counter for each process
  Sample,  \* [loopProc -> subset of query processes] for current round
  Iter     \* [loopProc -> Nat] number of completed iterations

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ Color = [n \in Node |-> NoColor]
  /\ Msgs  = {}
  /\ PC    = [p \in Proc |
                IF p = "Client"          THEN "Assign"
                ELSE IF p \in SlushLoopProcess THEN "WaitAssign"
                ELSE "ReplyLoop"]
  /\ Sample = [lp \in SlushLoopProcess |-> {}]
  /\ Iter   = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Action: client assigns a random color to an uncolored node
AssignColor ==
  /\ PC["Client"] = "Assign"
  /\ \E n \in Node :
        /\ Color[n] = NoColor
        /\ LET c == CHOOSE col \in Colors : TRUE IN
           /\ Color' = [Color EXCEPT ![n] = c]
           /\ UNCHANGED <<Msgs, PC, Sample, Iter>>
  /\ PC' = [PC EXCEPT !["Client"] =
               IF \A n \in Node : Color'[n] # NoColor
               THEN "Done"
               ELSE "Assign"]

\* ----------------------------------------------------------------------
\* Loop process starts sampling once its host node is colored
StartSampling ==
  /\ \E lp \in SlushLoopProcess :
        /\ PC[lp] = "WaitAssign"
        /\ LET n == NodeOfLoop(lp) IN Color[n] # NoColor
        /\ PC' = [PC EXCEPT ![lp] = "Sample"]
        /\ UNCHANGED <<Color, Msgs, Sample, Iter>>

\* ----------------------------------------------------------------------
\* Loop process selects a random sample and sends query messages
SendQueries ==
  /\ \E lp \in SlushLoopProcess :
        /\ PC[lp] = "Sample"
        /\ LET n == NodeOfLoop(lp) IN
           LET candidates == SlushQueryProcess \ { QueryOfNode(n) } IN
           /\ \E s \subseteq candidates :
                /\ Cardinality(s) = SampleSetSize
                /\ LET qmsgs == { [type  |-> "query",
                                   src   |-> lp,
                                   dst   |-> qp,
                                   color |-> Color[n]] : qp \in s } IN
                   /\ Msgs'   = Msgs \cup qmsgs
                   /\ Sample' = [Sample EXCEPT ![lp] = s]
                   /\ PC'     = [PC EXCEPT ![lp] = "WaitReplies"]
                   /\ UNCHANGED <<Color, Iter>>
  /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Query process handles an incoming query
HandleQuery ==
  /\ \E qp \in SlushQueryProcess :
        /\ \E m \in Msgs :
             /\ m.type = "query" /\ m.dst = qp
             /\ LET n == NodeOfQuery(qp) IN
                LET adoptedColor ==
                     IF Color[n] = NoColor THEN m.color ELSE Color[n] IN
                /\ Color' = [Color EXCEPT ![n] = adoptedColor]
                /\ LET reply == [type  |-> "reply",
                                 src   |-> qp,
                                 dst   |-> m.src,
                                 color |-> adoptedColor] IN
                   Msgs' = (Msgs \ {m}) \cup {reply}
                /\ UNCHANGED <<PC, Sample, Iter>>

\* ----------------------------------------------------------------------
\* Loop process processes replies once all have arrived
ProcessReplies ==
  /\ \E lp \in SlushLoopProcess :
        /\ PC[lp] = "WaitReplies"
        /\ LET s == Sample[lp] IN
           LET replies == { m \in Msgs :
                             m.type = "reply" /\ m.dst = lp } IN
           /\ Cardinality(replies) = SampleSetSize
           /\ LET cnt(c) == Cardinality({ m \in replies : m.color = c }) IN
              LET n == NodeOfLoop(lp) IN
              LET newColor ==
                 IF cnt("Red") >= PickFlipThreshold THEN "Red"
                 ELSE IF cnt("Blue") >= PickFlipThreshold THEN "Blue"
                 ELSE Color[n] IN
              LET newIter == @ + 1 IN
                 Color'   = [Color EXCEPT ![n] = newColor]
                 Sample'  = [Sample EXCEPT ![lp] = {}]
                 Iter'    = [Iter EXCEPT ![lp] = newIter]
                 Msgs'    = Msgs \ replies
                 /\ LET pcVal ==
                        IF newIter = SlushIterationCount
                        THEN "Done"
                        ELSE "Sample" IN
                    PC' = [PC EXCEPT ![lp] = pcVal]
                 /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Query processes exit when every loop process has finished
QueryExit ==
  /\ \A lp \in SlushLoopProcess : PC[lp] = "Done"
  /\ \E qp \in SlushQueryProcess :
        /\ PC[qp] = "ReplyLoop"
        /\ PC' = [PC EXCEPT ![qp] = "Done"]
        /\ UNCHANGED <<Color, Msgs, Sample, Iter>>

\* ----------------------------------------------------------------------
\* The overall next-state relation
Next ==
  \/ AssignColor
  \/ StartSampling
  \/ SendQueries
  \/ HandleQuery
  \/ ProcessReplies
  \/ QueryExit

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<Color, Msgs, PC, Sample, Iter>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
  /\ Color \in [Node -> (Colors \cup {NoColor})]
  /\ Msgs  \subseteq Message
  /\ PC    \in [Proc -> {"Assign","Done","WaitAssign","Sample",
                        "WaitReplies","ReplyLoop"}]
  /\ Sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ Iter   \in [SlushLoopProcess -> Nat]

=====================================================================