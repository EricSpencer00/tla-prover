---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal

NoBlock == [sender |-> NoBlockVal, pred |-> NoHashVal, ptype |-> "no", tgt |-> NoBlockVal, amt |-> 0]

RECURSIVE SumAll(_)
SumAll(S) ==
  IF S = {} THEN 0
  ELSE LET n == CHOOSE x \in S : TRUE IN Ledger[CHOOSE e \in S : e = n][n].amt + SumAll(S \ {n})

RECURSIVE AccountBalance(_, _)
AccountBalance(ledger, h) ==
  IF h = NoHashVal THEN 0
  ELSE LET blk == ledger[h] IN
    IF blk.ptype = "no" THEN 0
    ELSE IF blk.ptype = "genesis" THEN blk.amt
    ELSE IF blk.ptype = "send" THEN -(blk.amt)
    ELSE IF blk.ptype = "receive" THEN blk.amt
    ELSE 0 + AccountBalance(ledger, blk.pred)

PUBLIC == {n \in Node : \E k \in PrivateKey : k \in OwnerOf[n]}

VARIABLES lastHash, Ledger, Received

vars == <<lastHash, Ledger, Received>>

TypeOK ==
  /\ lastHash \in (Hash \cup {NoHashVal})
  /\ Ledger \in [Node -> [Hash -> [sender : PublicKey, pred : Hash \cup {NoHashVal}, ptype : {"no"}, tgt : PublicKey, amt : 0]]]
  /\ Received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ Received = [n \in Node |-> {}]

ValidateBlock(n, h) ==
  /\ Ledger[n][h].sender \in PUBLIC
  /\ Ledger[n][h].pred = NoHashVal \/ Ledger[n][Ledger[n][h].pred].sender \in PUBLIC
  /\ CASE h \in Received[n] ->
        CASE Ledger[n][h].ptype = "send" ->
            /\ h \in Received[n]
            LET senderBal == AccountBalance(Ledger[n], Ledger[n][h].pred) IN
              /\ senderBal >= Ledger[n][h].amt
              /\ Ledger' = [Ledger EXCEPT ![n][h] = Ledger[n][h]]
              /\ Received' = [Received EXCEPT ![n] = Received[n] \ {h}]
        OTHER ->
          /\ Ledger' = Ledger
          /\ Received' = Received
     OTHER ->
        /\ Ledger' = Ledger
        /\ Received' = Received
  /\ UNCHANGED lastHash

CreateGenesis(n, k) ==
  /\ lastHash = NoHashVal
  /\ k \in OwnerOf[n]
  /\ \A m \in Node : Ledger[m][NoHashVal].ptype = "no"
  /\ \E h \in Hash :
       /\ Ledger' = [m \in Node |-> [Ledger[m] EXCEPT ![h] = [sender |-> PublicKeyOf[k], pred |-> NoHashVal, ptype |-> "genesis", tgt |-> PublicKeyOf[k], amt |-> GenesisBalance]]]
       /\ Received' = [m \in Node |-> Received[m] \cup {h}]
  /\ UNCHANGED lastHash

CreateSend(n, k, h, amt) ==
  /\ h \notin Received[n]
  /\ lastHash # NoHashVal
  /\ k \in OwnerOf[n]
  /\ \E nh \in Hash :
       /\ Ledger' = [Ledger EXCEPT ![n][nh] = [sender |-> PublicKeyOf[k], pred |-> lastHash, ptype |-> "send", tgt |-> PublicKeyOf[k], amt |-> amt]]
       /\ Received' = [Received EXCEPT ![n] = Received[n] \cup {nh}]
  /\ UNCHANGED lastHash

CreateOpen(n, k, h) ==
  /\ h \notin Received[n]
  /\ lastHash # NoHashVal
  /\ k \in OwnerOf[n]
  /\ \E nh \in Hash :
       /\ Ledger' = [Ledger EXCEPT ![n][nh] = [sender |-> PublicKeyOf[k], pred |-> lastHash, ptype |-> "open", tgt |-> PublicKeyOf[k], amt |-> 0]]
       /\ Received' = [Received EXCEPT ![n] = Received[n] \cup {nh}]
  /\ UNCHANGED lastHash

CreateReceive(n, k, h, src) ==
  /\ h \notin Received[n]
  /\ lastHash # NoHashVal
  /\ k \in OwnerOf[n]
  /\ src \in Hash
  /\ \A m \in Node : Ledger[m][src].ptype = "send"
  /\ \E nh \in Hash :
       /\ Ledger' = [Ledger EXCEPT ![n][nh] = [sender |-> PublicKeyOf[k], pred |-> lastHash, ptype |-> "receive", tgt |-> PublicKeyOf[k], amt |-> Ledger[n][src].amt]]
       /\ Received' = [Received EXCEPT ![n] = Received[n] \cup {nh}]
  /\ UNCHANGED lastHash

Next == \E n \in Node, k \in PrivateKey :
  \/ CreateGenesis(n, k)
  \/ \E h \in Hash, amt \in 0..GenesisBalance : CreateSend(n, k, h, amt) \/ CreateOpen(n, k, h) \/ CreateReceive(n, k, h, NoBlockVal)
  \/ \E h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

SafetyInvariant ==
  /\ TypeOK
  /\ \A n \in Node, h \in Hash : Ledger[n][h].ptype # "no" => VerifySignature(PublicKeyOf[OwnerOf[n]], Ledger[n][h].sender)

====