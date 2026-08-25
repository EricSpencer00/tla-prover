---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS 
    Node,                     \* set of all nodes
    SlushLoopProcess,         \* one loop process per node
    SlushQueryProcess,        \* one query process per node
    HostMapping,              \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,      \* number of iterations each loop performs
    SampleSetSize,            \* size of the sampling set
    PickFlipThreshold,        \* threshold to flip color
    NoColor,                  \* special value meaning “uncolored”
    NoMessage                 \* unused placeholder for “no message”

\* ----------------------------------------------------------------------
\* PlusCal algorithm that models the Slush protocol
\* ----------------------------------------------------------------------
\*--algorithm SlushAlg
variables
    \* current color of every node; initially all uncolored
    color = [n \in Node |-> NoColor],
    \* in‑flight messages (each a record)
    msgs  = {},
    \* program counters for every process (including the client)
    pc    = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "Init"],
    \* the current sampling set for each loop process
    sample = [l \in SlushLoopProcess |-> {}],
    \* iteration counter for each loop process
    iter   = [l \in SlushLoopProcess |-> 0]

define
    \* return the node that belongs to a given loop process
    NodeOfLoop(l) == 
        CHOOSE n \in Node : \E q \in SlushQueryProcess :
                         <<n, l, q>> \in HostMapping

    \* return the node that belongs to a given query process
    NodeOfQuery(q) == 
        CHOOSE n \in Node : \E lp \in SlushLoopProcess :
                         <<n, lp, q>> \in HostMapping

    \* the set of nodes other than the given one
    OtherNodes(n) == Node \ {n}

    \* a nondeterministic choice of a subset of the required size
    RandomSample(n) == 
        { s \in SUBSET OtherNodes(n) : Cardinality(s) = SampleSetSize }

    \* the threshold used when counting replies
    FlipThreshold == PickFlipThreshold
end define;

\* ----------------------------------------------------------------------
\* Client process: repeatedly assign a random color to an uncolored node
\* ----------------------------------------------------------------------
process (client = "client")
begin
  ClientAssign:
    while \E n \in Node : color[n] = NoColor do
      with n \in { n \in Node : color[n] = NoColor } do
        with c \in {"Red","Blue"} do
          color := [color EXCEPT ![n] = c];
          pc   := [pc EXCEPT !["client"] = "ClientAssign"];
        end with;
      end with;
    end while;
    pc := [pc EXCEPT !["client"] = "Done"];
end process;

\* ----------------------------------------------------------------------
\* Loop process: performs the Slush sampling / tally / possible flip
\* ----------------------------------------------------------------------
process (loop = SlushLoopProcess)
begin
  RequireColor:
    await color[NodeOfLoop(self)] # NoColor;
    pc := [pc EXCEPT ![self] = "Sample"];

  Sample:
    with s \in RandomSample(NodeOfLoop(self)) do
      sample := [sample EXCEPT ![self] = s];
      \* send a query to each sampled node's query process
      with qproc \in { q \in SlushQueryProcess :
                         \E n \in Node : 
                           <<n, self, q>> \in HostMapping } do
        msgs := msgs \cup {
                    [type |-> "query",
                     src  |-> self,
                     dst  |-> qproc,
                     color|-> color[NodeOfLoop(self)]]
                 };
      end with;
    end with;
    pc := [pc EXCEPT ![self] = "Collect"];

  Collect:
    \* wait for a reply from every sampled peer
    await \A n \in sample[self] :
            \E m \in msgs :
               /\ m.type = "reply"
               /\ m.dst  = self
               /\ m.src  = (CHOOSE q \in SlushQueryProcess :
                               \E lp \in SlushLoopProcess :
                                 <<n, lp, q>> \in HostMapping);
    \* tally the replies
    let replies == { m \in msgs : m.type = "reply" /\ m.dst = self } in
    let redCnt  == Cardinality({ m \in replies : m.color = "Red" }) in
    let blueCnt == Cardinality({ m \in replies : m.color = "Blue" }) in
        if redCnt >= FlipThreshold then
            color := [color EXCEPT ![NodeOfLoop(self)] = "Red"]
        elsif blueCnt >= FlipThreshold then
            color := [color EXCEPT ![NodeOfLoop(self)] = "Blue"]
        else
            UNCHANGED color
        endif;
    \* (optional) send a self‑reply so the loop can observe its own color;
    \* not required by the protocol but keeps the model simple
    msgs := msgs \cup {
                [type |-> "reply",
                 src  |-> self,
                 dst  |-> self,
                 color|-> color[NodeOfLoop(self)]]
            };
    sample := [sample EXCEPT ![self] = {}];
    iter   := [iter EXCEPT ![self] = @ + 1];
    if iter[self] >= SlushIterationCount then
        pc := [pc EXCEPT ![self] = "Terminate"]
    else
        pc := [pc EXCEPT ![self] = "Sample"]
    endif;

  Terminate:
    msgs := msgs \cup {
                [type |-> "term",
                 src  |-> self,
                 dst  |-> "all",
                 color|-> NoColor]
            };
    pc := [pc EXCEPT ![self] = "Done"];
end process;

\* ----------------------------------------------------------------------
\* Query process: answers queries and may adopt a color if uncolored
\* ----------------------------------------------------------------------
process (query = SlushQueryProcess)
begin
  ReplyLoop:
    while TRUE do
      await \E m \in msgs :
               /\ m.type = "query"
               /\ m.dst  = self;
      with m \in { m \in msgs :
                    m.type = "query" /\ m.dst = self } do
        \* possibly adopt the queried color
        if color[NodeOfQuery(self)] = NoColor then
            color := [color EXCEPT ![NodeOfQuery(self)] = m.color];
        else
            UNCHANGED color;
        endif;
        \* reply with the (maybe newly adopted) color
        msgs := msgs \cup {
                    [type |-> "reply",
                     src  |-> self,
                     dst  |-> m.src,
                     color|-> color[NodeOfQuery(self)]]
                 };
      end with;
    end while;
    pc := [pc EXCEPT ![self] = "Done"];
end process;

end algorithm;

\* ----------------------------------------------------------------------
\* End of PlusCal algorithm
\* ----------------------------------------------------------------------
\* The PlusCal translation creates the following TLA+ operators:
\*   Init  – the initial predicate,
\*   Next  – the disjunction of all actions,
\*   vars  – the tuple of all variables.
\* ----------------------------------------------------------------------
vars == <<color, msgs, pc, sample, iter>>

Init == SlushAlg!Init

Next == SlushAlg!Next

\* The overall specification
Spec == Init /\ [][Next]_vars

\* Type invariant required by the configuration
TypeInvariant ==
    /\ color \in [Node -> ({"Red","Blue"} \cup {NoColor})]
    /\ msgs \subseteq {
            [type  : {"query","reply","term"},
             src   : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
             dst   : (SlushLoopProcess \cup SlushQueryProcess \cup {"all"}),
             color : ({"Red","Blue"} \cup {NoColor})]
         }
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) ->
                {"Init","ClientAssign","RequireColor","Sample",
                 "Collect","Terminate","ReplyLoop","Done"} ]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter   \in [SlushLoopProcess -> Nat]

====