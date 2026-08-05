---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush is the simplest member of the Snow family of probabilistic consensus
\* protocols (Avalanche whitepaper); each node independently repeats a query
\* round on a random sample of peers and adopts a popular opinion.  The query
\* processes model the gossip path: a node only learns about a peer's opinion
\* by receiving a query reply rather than peeking at the peer's state directly.
\* Because TLA+ has no probabilistic modeling, this executable design is
\* intended as a deterministic counterpart rather than a full verification of
\* Slush's metastability guarantee.
CONSTANTS
  Node
  SlushLoopProcess
  SlushQueryProcess
  HostMapping
  SlushIterationCount
  SampleSetSize
  PickFlipThreshold
  NoColor
  NoMessage

ASSUME SlushLoopProcess = 1..Cardinality(Node)
ASSUME SlushQueryProcess = 1..Cardinality(Node)
ASSUME \A n \in Node : Cardinality({x \in HostMapping : x[1] = n}) = 1

MessageType == [type : {"query", "queryReply", "termination"}, sender : SlushQueryProcess, receiver : SlushLoopProcess, color : 0..2, query : 0..2]

VARIABLES
  colorAssignment     \* [node \in Node -> 0..2] current color per node, or NoColor
  messages            \* set of in-flight messages of type MessageType
  processPC           \* [SlushLoopProcess \cup SlushQueryProcess \cup {0} -> 0..5] program counter per process; 0 = client, 1 = waiting, 2 = sampled, 3 = tallying, 4 = done
  sampleSet           \* [SlushLoopProcess -> SUBSET SlushQueryProcess] peers queried this round
  iterationsDone      \* [SlushLoopProcess -> 0..SlushIterationCount] query rounds completed

TypeInvariant ==
  /\ colorAssignment \in [Node -> {0, 1, 2}]
  /\ messages \subseteq MessageType
  /\ processPC \in [SlushLoopProcess \cup SlushQueryProcess \cup {0} -> 0..5]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterationsDone \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ colorAssignment = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ processPC = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {0} |-> IF p = 0 THEN 1 ELSE 1]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ iterationsDone = [lp \in SlushLoopProcess |-> 0]

\* The client process is what lets Slush start: it assigns every node an
\* initial color (an external transaction) before any loop process can begin.
ClientAssignColor ==
  /\ processPC[0] = 1
  /\ \E n \in Node, col \in {1, 2} :
       /\ colorAssignment[n] = NoColor
       /\ colorAssignment' = [colorAssignment EXCEPT ![n] = col]
  /\ processPC' = [processPC EXCEPT ![0] = 0]
  /\ UNCHANGED <<messages, sampleSet, iterationsDone>>

RequireHostColor(lp) ==
  /\ processPC[lp] = 1
  /\ \E n \in Node : <<n, lp, 0>> \in HostMapping /\ colorAssignment[n] # NoColor
  /\ processPC' = [processPC EXCEPT ![lp] = 2]
  /\ UNCHANGED <<colorAssignment, messages, sampleSet, iterationsDone>>

QuerySampleSet(lp) ==
  /\ processPC[lp] = 2
  /\ iterationsDone[lp] < SlushIterationCount
  /\ \E s \in SUBSET SlushQueryProcess :
       /\ Cardinality(s) = SampleSetSize
       /\ \A x \in s : Cardinality({n \in Node : <<n, x, 0>> \in HostMapping}) = 1
       /\ messages' = messages \cup { [type |-> "query", sender |-> x, receiver |-> lp, color |-> colorAssignment[CHOOSE n \in Node : <<n, x, 0>> \in HostMapping], query |-> 0] : x \in s }
       /\ sampleSet' = [sampleSet EXCEPT ![lp] = s]
  /\ processPC' = [processPC EXCEPT ![lp] = 3]
  /\ UNCHANGED <<colorAssignment, iterationsDone>>

\* A query process never fails or drops a message: every query it receives is
\* answered, which is what keeps the Slush system strongly connected.
RespondQuery(mp) ==
  /\ mp \in messages
  /\ mp.type = "query"
  /\ LET n == CHOOSE ne \in Node : <<ne, mp.sender, 0>> \in HostMapping IN
     /\ colorAssignment' = [colorAssignment EXCEPT ![n] = IF colorAssignment[n] = NoColor THEN mp.color ELSE colorAssignment[n]]
     /\ messages' = (messages \ {mp}) \cup {[type |-> "queryReply", sender |-> mp.sender, receiver |-> lp, color |-> IF colorAssignment[n] = NoColor THEN mp.color ELSE colorAssignment[n], query |-> mp.color] : lp \in SlushLoopProcess : <<n, lp, 0>> \in HostMapping}
  /\ UNCHANGED <<processPC, sampleSet, iterationsDone>>

TallyReplies(lp) ==
  /\ processPC[lp] = 3
  /\ \A x \in sampleSet[lp] : \E mp \in messages : mp.type = "queryReply" /\ mp.sender = x /\ mp.receiver = lp
  /\ LET replies == {mp \in messages : mp.type = "queryReply" /\ mp.receiver = lp} IN
     /\ Cardinality({mp \in replies : mp.color = 1}) >= PickFlipThreshold => colorAssignment' = [colorAssignment EXCEPT ![CHOOSE n \in Node : <<n, lp, 0>> \in HostMapping] = 1]
     /\ Cardinality({mp \in replies : mp.color = 2}) >= PickFlipThreshold => colorAssignment' = [colorAssignment EXCEPT ![CHOOSE n \in Node : <<n, lp, 0>> \in HostMapping] = 2]
     /\ Cardinality({mp \in replies : mp.color > 0}) >= PickFlipThreshold => UNCHANGED colorAssignment
  /\ messages' = messages \ {mp \in messages : mp.type = "queryReply" /\ mp.receiver = lp}
  /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
  /\ iterationsDone' = [iterationsDone EXCEPT ![lp] = iterationsDone[lp] + 1]
  /\ processPC' = IF iterationsDone[lp] + 1 < SlushIterationCount THEN [processPC EXCEPT ![lp] = 2] ELSE [processPC EXCEPT ![lp] = 4]

LoopTermination(lp) ==
  /\ processPC[lp] = 4
  /\ processPC' = [processPC EXCEPT ![lp] = 5]
  /\ messages' = messages \cup {[type |-> "termination", sender |-> 0, receiver |-> lp, color |-> 0, query |-> 0]}
  /\ UNCHANGED <<colorAssignment, sampleSet, iterationsDone>>

QueryLoopExit ==
  /\ \A lp \in SlushLoopProcess : processPC[lp] = 5
  /\ \A x \in SlushQueryProcess : processPC[x] = 3
  /\ processPC' = [processPC EXCEPT ![x \in SlushQueryProcess] = 4]
  /\ UNCHANGED <<colorAssignment, messages, sampleSet, iterationsDone>>

Next ==
  \/ ClientAssignColor
  \/ QueryLoopExit
  \/ \E lp \in SlushLoopProcess : RequireHostColor(lp) \/ QuerySampleSet(lp) \/ TallyReplies(lp) \/ LoopTermination(lp)
  \/ \E mp \in messages : RespondQuery(mp)

Spec == Init /\ [][Next]_<<colorAssignment, messages, processPC, sampleSet, iterationsDone>>

EventualTermination == <>(\A lp \in SlushLoopProcess \cup SlushQueryProcess : processPC[lp] = 4)

====