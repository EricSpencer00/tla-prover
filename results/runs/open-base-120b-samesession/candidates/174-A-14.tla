---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

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

(* ------------------------------------------------------------------- *)
Colors == {"Red", "Blue", NoColor}
MessageType == {"query", "reply", "term"}
Message == [type : MessageType,
            src  : SlushLoopProcess \cup SlushQueryProcess,
            dst  : (SlushLoopProcess \cup SlushQueryProcess) \cup {"all"},
            col  : Colors]

NodeOf(lp) == 
  CHOOSE n \in Node :
    \E q \in SlushQueryProcess : <<n, lp, q>> \in HostMapping

QueryOf(lp) ==
  CHOOSE q \in SlushQueryProcess :
    <<NodeOf(lp), lp, q>> \in HostMapping

NodeOfQuery(qp) ==
  CHOOSE n \in Node :
    \E lp \in SlushLoopProcess : <<n, lp, qp>> \in HostMapping

(* ------------------------------------------------------------------- *)
\* BEGIN_ALGORITHM SlushAlg
variables
    color    = [n \in Node |-> NoColor],
    msgs     = {},
    pc       = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "Init"],
    sample   = [lp \in SlushLoopProcess |-> {}],
    iter     = [lp \in SlushLoopProcess |-> 0],
    termCount = 0;

process (client = "client")
{
  while TRUE do
    either
      /\ \E n \in Node : color[n] = NoColor
      /\ let chosen == CHOOSE n \in Node : color[n] = NoColor in
         let col == CHOOSE c \in {"Red","Blue"} : TRUE in
         color' = [color EXCEPT ![chosen] = col]
    or
      /\ UNCHANGED <<color, msgs, sample, iter, termCount, pc>>
    end either;
  end while;
}

process (lp \in SlushLoopProcess)
{
  while iter[lp] < SlushIterationCount do
    if color[NodeOf(lp)] = NoColor then
      skip               \* wait for a color assignment
    else
      \* --- sampling phase ---
      sample' = [sample EXCEPT ![lp] =
        CHOOSE s \subseteq (SlushQueryProcess \ {QueryOf(lp)}) :
          Cardinality(s) = SampleSetSize];
      \* send query messages
      msgs' = msgs \cup
        { [type |-> "query",
           src  |-> lp,
           dst  |-> q,
           col  |-> color[NodeOf(lp)] ] : q \in sample'[lp] };
      \* collect replies (modeled as instantaneous)
      let replies == { m \in msgs' : m.type = "reply" /\ m.dst = lp } in
      let redCnt  == Cardinality({ r \in replies : r.col = "Red" }) in
      let blueCnt == Cardinality({ r \in replies : r.col = "Blue" }) in
      if redCnt >= PickFlipThreshold then
        color' = [color EXCEPT ![NodeOf(lp)] = "Red"]
      elsif blueCnt >= PickFlipThreshold then
        color' = [color EXCEPT ![NodeOf(lp)] = "Blue"]
      else
        UNCHANGED color;
      \* clear sample and advance iteration
      sample' = [sample EXCEPT ![lp] = {}];
      iter'   = [iter EXCEPT ![lp] = @ + 1];
      \* remove processed replies
      msgs' = msgs' \ { m \in replies }
    end if;
  end while;
  \* termination broadcast
  msgs' = msgs \cup { [type |-> "term", src |-> lp, dst |-> "all", col |-> NoMessage] };
  termCount' = termCount + 1;
  pc' = [pc EXCEPT ![lp] = "Done"]
}

process (qp \in SlushQueryProcess)
{
  while TRUE do
    either
      /\ \E m \in msgs : m.type = "query" /\ m.dst = qp
      /\ let qmsg == CHOOSE m \in msgs : m.type = "query" /\ m.dst = qp in
         if color[NodeOfQuery(qp)] = NoColor then
           color' = [color EXCEPT ![NodeOfQuery(qp)] = qmsg.col]
         else
           UNCHANGED color;
         msgs' = msgs \cup
           { [type |-> "reply",
              src  |-> qp,
              dst  |-> qmsg.src,
              col  |-> color[NodeOfQuery(qp)]] };
         msgs' = msgs' \ { qmsg }
    or
      /\ \E m \in msgs : m.type = "term" /\ m.dst = "all"
      /\ termCount >= Cardinality(SlushLoopProcess)
         => skip   \* all loop processes have terminated
    or
      /\ UNCHANGED <<color, msgs>>
    end either;
  end while;
}
\* END_ALGORITHM

(* ------------------------------------------------------------------- *)
TypeInvariant ==
  /\ color \in [Node -> Colors]
  /\ msgs \subseteq Message
  /\ pc \in [(SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) -> STRING]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iter \in [SlushLoopProcess -> Nat]
  /\ termCount \in Nat

Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter, termCount>>

====