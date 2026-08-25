---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS 
    Node,               \* set of node identifiers
    SlushLoopProcess,   \* set of loop process identifiers
    SlushQueryProcess,  \* set of query process identifiers
    HostMapping,        \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,\* number of iterations each loop performs
    SampleSetSize,      \* size of the peer sample
    PickFlipThreshold,  \* threshold to flip the node's color
    NoColor,            \* sentinel for an uncolored node
    NoMessage           \* sentinel for an absent message

\* ----------------------------------------------------------------------
\* Derived sets and record types
\* ----------------------------------------------------------------------
Color == {"Red", "Blue"}

Process == SlushLoopProcess \cup SlushQueryProcess \cup {"client"}

Message == [type : {"query", "reply", "term"},
            src  : Process,
            dst  : Process,
            col  : NoColor \cup Color]

\* ----------------------------------------------------------------------
\* Helper functions extracting the node that a process hosts
\* ----------------------------------------------------------------------
NodeOfLoop(p) == 
    CHOOSE n \in Node : <<n, p, q>> \in HostMapping

NodeOfQuery(q) ==
    CHOOSE n \in Node : <<n, l, q>> \in HostMapping

QueryOfNode(n) ==
    CHOOSE q \in SlushQueryProcess : <<n, l, q>> \in HostMapping

\* ----------------------------------------------------------------------
\* PlusCal algorithm describing the behavior
\* ----------------------------------------------------------------------
(*--algorithm SlushAlg
variables
    color      = [n \in Node |-> NoColor],
    msgs       = {},
    pc         = [p \in Process |-> "Init"],
    sampleSet  = [p \in SlushLoopProcess |-> {}],
    iter       = [p \in SlushLoopProcess |-> 0];

process (client = "client")
{
  while TRUE do
    if \E n \in Node : color[n] = NoColor then
      with n \in { n \in Node : color[n] = NoColor } do
        with c \in Color do
          color := [color EXCEPT ![n] = c];
        end with;
      end with;
    else
      skip;
    end if;
  end while;
}

process (lp \in SlushLoopProcess)
{
  variable myNode;
  myNode := NodeOfLoop(self);
  while iter[self] < SlushIterationCount do
    /\* wait until the host node has a color *\/
    await color[myNode] # NoColor;

    /\* choose a random sample of peers *\/
    sampleSet := [sampleSet EXCEPT ![self] = 
                     CHOOSE S \subseteq (Node \ {myNode}) :
                       Cardinality(S) = SampleSetSize];

    /\* send a query to each sampled peer *\/
    for qNode \in sampleSet[self] do
      let dst == QueryOfNode(qNode) in
        msgs := msgs \cup {
          [type |-> "query",
           src  |-> self,
           dst  |-> dst,
           col  |-> color[myNode]]
        };
      end let;
    end for;

    /\* wait for replies from all sampled peers *\/
    await \A qNode \in sampleSet[self] :
          \E m \in msgs :
            /\* a reply from the query process of qNode *\/
            m.type = "reply" /\ m.src = QueryOfNode(qNode) /\ m.dst = self;

    /\* tally the replies *\/
    with redCnt == Cardinality({
          qNode \in sampleSet[self] :
            \E m \in msgs :
              m.type = "reply" /\ m.src = QueryOfNode(qNode) /\
              m.dst = self /\ m.col = "Red"
        }) do
      with blueCnt == Cardinality({
          qNode \in sampleSet[self] :
            \E m \in msgs :
              m.type = "reply" /\ m.src = QueryOfNode(qNode) /\
              m.dst = self /\ m.col = "Blue"
        }) do
        if redCnt >= PickFlipThreshold then
          color := [color EXCEPT ![myNode] = "Red"];
        elsif blueCnt >= PickFlipThreshold then
          color := [color EXCEPT ![myNode] = "Blue"];
        else
          skip;
        end if;
        /\* clean up for next round *\/
        sampleSet := [sampleSet EXCEPT ![self] = {}];
        iter      := [iter EXCEPT ![self] = @ + 1];
      end with;
    end with;
  end while;

  /\* broadcast termination to all query processes *\/
  for qp \in SlushQueryProcess do
    msgs := msgs \cup {
      [type |-> "term",
       src  |-> self,
       dst  |-> qp,
       col  |-> NoColor]
    };
  end for;
  pc := [pc EXCEPT ![self] = "Done"];
}

process (qp \in SlushQueryProcess)
{
  variable myNode;
  myNode := NodeOfQuery(self);
  while TRUE do
    /\* respond to any pending query *\/
    with m \in msgs :
         m.type = "query" /\ m.dst = self do
      if color[myNode] = NoColor then
        color := [color EXCEPT ![myNode] = m.col];
      end if;
      msgs := msgs \cup {
        [type |-> "reply",
         src  |-> self,
         dst  |-> m.src,
         col  |-> color[myNode]]
      };
    end with;

    /\* exit when termination received from every loop process *\/
    await \A lp \in SlushLoopProcess :
          \E t \in msgs :
            t.type = "term" /\ t.src = lp /\ t.dst = self;
    pc := [pc EXCEPT ![self] = "Done"];
    break;
  end while;
}
end algorithm;*)

\* ----------------------------------------------------------------------
\* TLA+ wrapper around the PlusCal translation
\* ----------------------------------------------------------------------
vars == <<color, msgs, pc, sampleSet, iter>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant (safety property)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> (NoColor \cup Color)]
    /\ msgs \subseteq Message

====