---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME CalculateHash \in [Hash -> Hash]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

RECURSIVE ChainHashes(_)
ChainHashes(h) ==
  IF h = NoHashVal THEN {}
  ELSE CHOOSE b \in ledger[NoHash][NoHash] : b.hash = h
       /\ {b.hash} \cup ChainHashes(b.prevHash)

RECURSIVE ChainSum(_)
ChainSum(h) ==
  IF h = NoHashVal THEN 0
  ELSE CHOOSE b \in ledger[NoHash][NoHash] : b.hash = h
       /\ b.amount + ChainSum(b.prevHash)

RECURSIVE AccountBalance(_)
AccountBalance(pub) == ChainSum(CHOOSE h \in Hash : h = NoHashVal /\ ~\E b \in ledger[NoHash][NoHash] : b.hash = h)

RECURSIVE AccountHash(_)
AccountHash(pub) ==
  IF pub \notin {b.pubKey : h \in Hash, b \in ledger[h][NoHash]} THEN NoHashVal
  ELSE CHOOSE h \in Hash :
    \E b \in ledger[h][NoHash] : b.pubKey = pub /\ \A g \in Hash : g < h => ~\E d \in ledger[g][NoHash] : d.pubKey = pub

RECURSIVE TotalBalances(_)
TotalBalances(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN AccountBalance(x) + TotalBalances(S \ {x})

TypeInvariant ==
  /\ lastHash \in Hash
  /\ ledger \in [Hash -> [Node -> {NoBlock} \union [hash : Hash, pk : PrivateKey, pubKey : PublicKey, prevHash : Hash, typ : {"genesis", "send", "open", "receive", "change"}, amount : 0..GenesisBalance]]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> [n \in Node |-> {NoBlock}]]
  /\ received = [n \in Node |-> {}]

BroadcastBlock(b) ==
  [n \in Node |-> received[n] \union {b.hash}]

GenesisBlock ==
  /\ lastHash = NoHashVal
  /\ \E c \in PrivateKey :
    /\ lastHash' = CalculateHash(lastHash)
    /\ ledger' = [h \in Hash |-> IF h = lastHash
        THEN [n \in Node |-> IF TRUE THEN { [hash |-> lastHash, pk |-> c, pubKey |-> ToPublic(c), prevHash |-> NoHashVal, typ |-> "genesis", amount |-> GenesisBalance] } ELSE {NoBlock}]
        ELSE ledger[h]]
    /\ received' = BroadcastBlock([hash |-> lastHash, pk |-> c, pubKey |-> ToPublic(c), prevHash |-> NoHashVal, typ |-> "genesis", amount |-> GenesisBalance])

SendBlock(n) ==
  /\ \E amt \in 1..GenesisBalance :
    /\ AccountBalance(ToPublic(PrivateKey \in Node)) >= amt
    /\ \E c \in PrivateKey :
      /\ lastHash' = CalculateHash(lastHash)
      /\ ledger' = [h \in Hash |-> IF h = lastHash
          THEN [n \in Node |-> IF TRUE THEN { [hash |-> lastHash, pk |-> c, pubKey |-> ToPublic(c), prevHash |-> AccountHash(ToPublic(c)), typ |-> "send", amount |-> amt] } ELSE {NoBlock}]
          ELSE ledger[h]]
      /\ received' = BroadcastBlock([hash |-> lastHash, pk |-> c, pubKey |-> ToPublic(c), prevHash |-> AccountHash(ToPublic(c)), typ |-> "send", amount |-> amt])

OpenBlock(n) ==
  /\ \E h \in Hash :
    /\ NoHashVal \notin ACCOUNTHASH(ToPublic(PrivateKey \in Node))
    /\ \E s \in ledger[h][n] :
      /\ s.typ = "send" /\ s.pubKey = ToPublic(PrivateKey \in Node)
      /\ lastHash' = CalculateHash(lastHash)
      /\ ledger' = [x \in Hash |-> IF x = lastHash
          THEN [m \in Node |-> IF TRUE THEN { [hash |-> lastHash, pk |-> s.pk, pubKey |-> s.pubKey, prevHash |-> NoHashVal, typ |-> "open", amount |-> 0] } ELSE {NoBlock}]
          ELSE ledger[x]]
      /\ received' = BroadcastBlock([hash |-> lastHash, pk |-> s.pk, pubKey |-> s.pubKey, prevHash |-> NoHashVal, typ |-> "open", amount |-> 0])

ReceiveBlock(n) ==
  /\ \E h \in Hash :
    /\ \E s \in ledger[h][n] :
      /\ s.typ = "send" /\ s.pubKey = ToPublic(PrivateKey \in Node)
      /\ lastHash' = CalculateHash(lastHash)
      /\ ledger' = [x \in Hash |-> IF x = lastHash
          THEN [m \in Node |-> IF TRUE THEN { [hash |-> lastHash, pk |-> s.pk, pubKey |-> s.pubKey, prevHash |-> AccountHash(s.pubKey), typ |-> "receive", amount |-> 0] } ELSE {NoBlock}]
          ELSE ledger[x]]
      /\ received' = BroadcastBlock([hash |-> lastHash, pk |-> s.pk, pubKey |-> s.pubKey, prevHash |-> AccountHash(s.pubKey), typ |-> "receive", amount |-> 0])

ChangeBlock(n) ==
  /\ \E c \in PrivateKey :
    /\ lastHash' = CalculateHash(lastHash)
    /\ ledger' = [h \in Hash |-> IF h = lastHash
        THEN [m \in Node |-> IF TRUE THEN { [hash |-> lastHash, pk |-> c, pubKey |-> ToPublic(c), prevHash |-> AccountHash(ToPublic(c)), typ |-> "change", amount |-> 0] } ELSE {NoBlock}]
        ELSE ledger[h]]
    /\ received' = BroadcastBlock([hash |-> lastHash, pk |-> c, pubKey |-> ToPublic(c), prevHash |-> AccountHash(ToPublic(c)), typ |-> "change", amount |-> 0])

Validate(n) ==
  /\ \E h \in received[n] :
    /\ \E s \in ledger[h][NoHash] :
      /\ s.pubKey = ToPublic(\E c \in PrivateKey : c = s.pk)
      /\ ledger' = [ledger EXCEPT ![s.prevHash][n] = @ \union {s}]
    /\ received' = [received EXCEPT ![n] = @ \ {h}]
    /\ UNCHANGED lastHash

Next ==
  \/ GenesisBlock
  \/ \E n \in Node : SendBlock(n)
  \/ \E n \in Node : OpenBlock(n)
  \/ \E n \in Node : ReceiveBlock(n)
  \/ \E n \in Node : ChangeBlock(n)
  \/ \E n \in Node : Validate(n)

Spec == Init /\ [][Next]_vars

SafetyInvariant ==
  \A n \in Node :
    \A h \in Hash :
      \A b \in ledger[h][n] :
        b.pubKey = ToPublic(\E c \in PrivateKey : c = b.pk)

====