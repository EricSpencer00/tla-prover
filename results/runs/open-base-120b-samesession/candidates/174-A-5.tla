---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

(* --algorithm SlushAlg
variables
    color = [n \in Node |-> NoColor],
    msgs  = {},
    sample = [l \in SlushLoopProcess |-> {}],
    iter   = [l \in SlushLoopProcess |-> 0];

define
    LoopNode == [l \in SlushLoopProcess |-> 
        CHOOSE n \in Node : <<l, _, n>> \in HostMapping];
    QueryNode == [q \in SlushQueryProcess |-> 
        CHOOSE n \in Node : <<_, q, n>> \in HostMapping];
    Colors == {"Red","Blue"};
    Message == [type : {"query","reply","term"},
                src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
                dst  : (SlushLoopProcess \cup SlushQueryProcess),
                col  : (Colors \cup {NoColor})];
    SelectSubset(S, k) == 
        CHOOSE sub \in SUBSET S : Cardinality(sub) = k;
end define;

process (client = "client")
begin
ClientLoop:
  while TRUE do
    with n \in Node do
      if color[n] = NoColor then
        with col \in Colors do
          color := [color EXCEPT ![n] = col];
        end with;
      end if;
    end with;
    if \A n \in Node : color[n] # NoColor then
      goto DoneClient;
    end if;
  end while;
DoneClient:
  skip;
end process;

process (loop = SlushLoopProcess)
variable l \in SlushLoopProcess;
begin
LoopBody:
  while iter[l] < SlushIterationCount do
    \* wait until the host node is colored
    while color[LoopNode[l]] = NoColor do
      skip;
    end while;

    \* select a random sample of peers
    with peers == { q \in SlushQueryProcess : QueryNode[q] # LoopNode[l] } do
      with s == SelectSubset(peers, SampleSetSize) do
        sample[l] := s;
        \* send a query to each sampled peer
        with each q \in s do
          msgs := msgs \cup { [type |-> "query",
                               src  |-> l,
                               dst  |-> q,
                               col  |-> color[LoopNode[l]] ] };
        end with;
      end with;
    end with;

    \* wait for replies from all sampled peers
    while \E m \in msgs :
            /\ m.type = "reply"
            /\ m.dst = l
            /\ m.src \in sample[l] = FALSE do
      skip;
    end while;

    \* tally the replies
    with replies == { m \in msgs : m.type = "reply" /\ m.dst = l } do
      with redCnt == Cardinality({ m \in replies : m.col = "Red" }) do
        with blueCnt == Cardinality({ m \in replies : m.col = "Blue" }) do
          if redCnt >= PickFlipThreshold then
            color := [color EXCEPT ![LoopNode[l]] = "Red"];
          elsif blueCnt >= PickFlipThreshold then
            color := [color EXCEPT ![LoopNode[l]] = "Blue"];
          else
            skip;
          end if;
        end with;
      end with;
      \* clean up for the next round
      msgs   := msgs \ { m \in msgs : m.dst = l };
      sample[l] := {};
      iter[l] := iter[l] + 1;
    end with;
  end while;

  \* broadcast termination to all query processes
  with each q \in SlushQueryProcess do
    msgs := msgs \cup { [type |-> "term",
                         src  |-> l,
                         dst  |-> q,
                         col  |-> NoColor] };
  end with;
  skip;
end process;

process (query = SlushQueryProcess)
variable q \in SlushQueryProcess;
begin
QueryLoop:
  while TRUE do
    either
      /\ \E m \in msgs :
            /\ m.type = "query"
            /\ m.dst = q
      /\ let src == m.src, c == m.col in
            if color[QueryNode[q]] = NoColor then
              color := [color EXCEPT ![QueryNode[q]] = c];
            end if;
            msgs := (msgs \ {m}) \cup
                    { [type |-> "reply",
                       src  |-> q,
                       dst  |-> src,
                       col  |-> color[QueryNode[q]] ] };
    or
      /\ \E m \in msgs :
            /\ m.type = "term"
            /\ m.dst = q
      /\ msgs := msgs \ {m};
    or
      skip;
    end either;
  end while;
end process;
end algorithm *)

VARIABLES color, msgs, sample, iter

Init == 
    /\ color = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ sample = [l \in SlushLoopProcess |-> {}]
    /\ iter = [l \in SlushLoopProcess |-> 0]

Spec == Init /\ [][Next]_<<pc, color, msgs, sample, iter>>

TypeInvariant == 
    /\ color \in [Node -> ( {"Red","Blue"} \cup {NoColor} )]
    /\ msgs \subseteq [type : {"query","reply","term"},
                      src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
                      dst  : (SlushLoopProcess \cup SlushQueryProcess),
                      col  : ( {"Red","Blue"} \cup {NoColor})]

=============================================================================