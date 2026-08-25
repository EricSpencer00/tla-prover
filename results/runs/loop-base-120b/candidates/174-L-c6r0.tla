---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Node,
    SlushLoopProcess,
    SlushQueryProcess,
    HostMapping,
    SlushIterationCount,
    SampleSetSize,
    PickFlipThreshold,
    NoColor,
    NoMessage

(*--algorithm SlushAlg
variables
    color = [n \in Node |-> NoColor],
    msgs  = {},
    iter  = [l \in SlushLoopProcess |-> 0],
    sample = [l \in SlushLoopProcess |-> {}];

define
    NodeOfLoop(l) == 
        CHOOSE n \in Node : \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping;
    QueryOfNode(n) == 
        CHOOSE q \in SlushQueryProcess : \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping;
    Colors == {"Red","Blue"};
    QueryMsg(to, from, col) == [type |-> "query", to |-> to, from |-> from, col |-> col];
    ReplyMsg(to, from, col) == [type |-> "reply", to |-> to, from |-> from, col |-> col];
    TermMsg(to, from)       == [type |-> "term",  to |-> to, from |-> from];
end define;

process (Client = "client")
{
  while TRUE do
    with n \in Node:
      /\ color[n] = NoColor
      /\ col \in Colors
    do
      color' = [color EXCEPT ![n] = col];
    end with;
    if \A n \in Node : color[n] # NoColor then
      skip;
    end if;
  end while;
}

process (Loop = SlushLoopProcess)
{
  variable myNode;
  myNode := NodeOfLoop(self);
  while iter[self] < SlushIterationCount do
    /\ color[myNode] # NoColor;
    (* sample peers *)
    with S \subseteq (Node \ {myNode}):
      /\ Cardinality(S) = SampleSetSize
    do
      sample' = [sample EXCEPT ![self] = S];
      (* send queries *)
      with n \in S do
        let q == QueryOfNode(n) in
          msgs' = msgs \cup { QueryMsg(q, self, color[myNode]) };
        end with;
    end with;
    (* wait for replies from all sampled peers *)
    await \A n \in sample[self] :
      \E m \in msgs :
        /\ m.type = "reply"
        /\ m.to   = self
        /\ m.from = QueryOfNode(n);
    (* tally replies *)
    let reds  == Cardinality({ m \in msgs :
                               /\ m.type = "reply"
                               /\ m.to   = self
                               /\ m.col  = "Red" });
        blues == Cardinality({ m \in msgs :
                               /\ m.type = "reply"
                               /\ m.to   = self
                               /\ m.col  = "Blue" }) in
      if reds  >= PickFlipThreshold then
        color' = [color EXCEPT ![myNode] = "Red"];
      elsif blues >= PickFlipThreshold then
        color' = [color EXCEPT ![myNode] = "Blue"];
      else
        skip;
      end if;
    end;
    (* clear sample and increment iteration *)
    sample' = [sample EXCEPT ![self] = {}];
    iter'   = [iter   EXCEPT ![self] = @ + 1];
    if iter'[self] = SlushIterationCount then
      (* broadcast termination *)
      with q \in SlushQueryProcess do
        msgs' = msgs \cup { TermMsg(q, self) };
      end with;
    end if;
  end while;
}

process (Query = SlushQueryProcess)
{
  variable myNode;
  myNode := CHOOSE n \in Node : \E l \in SlushLoopProcess : <<n,l,self>> \in HostMapping;
  while TRUE do
    either
      await \E m \in msgs :
        /\ m.type = "query"
        /\ m.to   = self;
      let m == CHOOSE m \in msgs :
                /\ m.type = "query"
                /\ m.to   = self in
        if color[myNode] = NoColor then
          color' = [color EXCEPT ![myNode] = m.col];
        end if;
        msgs' = msgs \cup { ReplyMsg(m.from, self, color[myNode]) };
        msgs' = msgs' \ { m };
      end let;
    or
      await \E m \in msgs :
        /\ m.type = "term"
        /\ m.to   = self;
      (* termination received, exit loop *)
      skip;
    end either;
    if \A l \in SlushLoopProcess : iter[l] = SlushIterationCount then
      break;
    end if;
  end while;
}
end algorithm; *)

VARIABLES color, msgs, iter, sample

Spec == Init /\ [][Next]_<<color, msgs, iter, sample>>

TypeInvariant ==
    /\ \A n \in Node : color[n] \in {"Red","Blue", NoColor}
    /\ \A m \in msgs :
        /\ m.type \in {"query","reply","term"}
        /\ (m.type = "query" => 
                /\ m.to   \in SlushQueryProcess
                /\ m.from \in SlushLoopProcess
                /\ m.col  \in {"Red","Blue"})
        /\ (m.type = "reply" => 
                /\ m.to   \in SlushLoopProcess
                /\ m.from \in SlushQueryProcess
                /\ m.col  \in {"Red","Blue"})
        /\ (m.type = "term" => 
                /\ m.to   \in SlushQueryProcess
                /\ m.from \in SlushLoopProcess)

====