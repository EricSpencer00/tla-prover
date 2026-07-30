---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoBlock, NoHash, NoHashVal

VARIABLES lastHash, ledger, receivedSet, balanceCache

vars == <<lastHash, ledger, receivedSet, balanceCache>>

\* A block on an account's chain. chainId is the owning account's public key,
\* prev is the previous block in that account's chain, recipient is the
\* destination of a send, and sig is the creator's Ed25519 signature.
Block == [chainId: PublicKey, prev: Hash \cup {NoHash}, kind: {"genesis", "send", "open", "receive", "change"}, recipient: PublicKey \cup {NoBlock}, amount: 0..GenesisBalance, sig: PrivateKey]

\* The block hashes are a finite set; CalculateHash is an opaque operator that
\* maps block data and the previous hash to a new hash.
\* The .cfg file substitutes an implementation for CalculateHash.
CalculateHash == NoHash
\* The .cfg file substitutes an implementation for CalculateHashImpl.
CalculateHashImpl == NoHash

RECURSIVE BalanceOf(_, _)
BalanceOf(acc, h) ==
  IF h = NoHash THEN 0
  ELSE
    LET blk == ledger[acc][h] IN
      IF blk = NoBlockVal THEN 0
      ELSE IF blk.kind = "genesis" THEN blk.amount
      ELSE IF blk.kind = "open" THEN blk.amount
      ELSE IF blk.kind = "receive" THEN BalanceOf(acc, blk.prev) + blk.amount
      ELSE BalanceOf(acc, blk.prev)

RECURSIVE Accumulate(_, _, _)
Accumulate(nodes, n, h) ==
  IF n = 0 THEN 0
  ELSE
    LET nd == nodes[n]
        blk == ledger[nd][h]
    IN IF blk = NoBlockVal THEN Accumulate(nodes, n - 1, h)
       ELSE IF blk.kind = "genesis" THEN blk.amount + Accumulate(nodes, n - 1, h)
       ELSE IF blk.kind = "open" THEN blk.amount + Accumulate(nodes, n - 1, h)
       ELSE IF blk.kind = "receive" THEN blk.amount + Accumulate(nodes, n - 1, h)
       ELSE Accumulate(nodes, n - 1, h)

RECURSIVE AccountBalances(_, _)
AccountBalances(accs, n) ==
  IF n = 0 THEN 0
  ELSE AccountBalances(accs, n - 1) + BalanceOf(accs[n], lastHash)

InitCache ==
  [n \in Node |-> CHOOSE acc \in PublicKey : TRUE]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ receivedSet \in [Node -> SUBSET Hash]
  /\ balanceCache \in [Node -> PublicKey]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ receivedSet = [n \in Node |-> {}]
  /\ balanceCache = InitCache

\* Genesis is a one-shot event, so it requires NoHash for the last hash.
BeginGenesis ==
  /\ lastHash = NoHash
  /\ balanceCache \in [Node -> PublicKey]
  /\ \E pk \in PrivateKey :
      /\ balanceCache[pk] = balanceCache[balanceCache \in {pk}]
      /\ lastHash' = CalculateHashImpl([kind |-> "genesis", amount |-> GenesisBalance, chainId |-> balanceCache[pk], prev |-> NoHash, recipient |-> NoBlock], NoHash)
      /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [kind |-> "genesis", amount |-> GenesisBalance, chainId |-> balanceCache[pk], prev |-> NoHash, recipient |-> NoBlock, sig |-> pk]]]
  /\ receivedSet' = [n \in Node |-> receivedSet[n]]
  /\ balanceCache' = balanceCache

CreateSend(n) ==
  /\ lastHash # NoHash
  /\ BalanceOf(balanceCache[n], lastHash) > 0
  /\ \E pk \in PrivateKey :
       /\ pk # n
       /\ lastHash' = CalculateHashImpl([kind |-> "send", amount |-> 1, chainId |-> balanceCache[n], prev |-> lastHash, recipient |-> balanceCache[pk]], lastHash)
       /\ ledger' = [n2 \in Node |-> [ledger[n2] EXCEPT ![lastHash'] = [kind |-> "send", amount |-> 1, chainId |-> balanceCache[n], prev |-> lastHash, recipient |-> balanceCache[pk], sig |-> pk]]]
  /\ receivedSet' = [n2 \in Node |-> @ \cup {lastHash'}]
  /\ balanceCache' = balanceCache

CreateOpen(n) ==
  /\ lastHash # NoHash
  /\ \E pk \in PrivateKey :
       /\ pk # n
       /\ ledger[n][lastHash].kind = "send"
       /\ ledger[n][lastHash].recipient = balanceCache[pk]
       /\ ~\E h \in Hash : ledger[pk][h] # NoBlockVal /\ h >= lastHash
       /\ lastHash' = CalculateHashImpl([kind |-> "open", amount |-> 1, chainId |-> balanceCache[pk], prev |-> NoHash, recipient |-> NoBlock], lastHash)
       /\ ledger' = [n2 \in Node |-> [ledger[n2] EXCEPT ![lastHash'] = [kind |-> "open", amount |-> 1, chainId |-> balanceCache[pk], prev |-> NoHash, recipient |-> NoBlock, sig |-> n]]]
  /\ receivedSet' = [n2 \in Node |-> @ \cup {lastHash'}]
  /\ balanceCache' = balanceCache

CreateReceive(n) ==
  /\ lastHash # NoHash
  /\ \E pk \in PrivateKey :
       /\ pk # n
       /\ ledger[n][lastHash].kind = "send"
       /\ ledger[n][lastHash].recipient = balanceCache[pk]
       /\ ledger[pk][lastHash] = NoBlockVal
       /\ lastHash' = CalculateHashImpl([kind |-> "receive", amount |-> 1, chainId |-> balanceCache[pk], prev |-> lastHash, recipient |-> NoBlock], lastHash)
       /\ ledger' = [n2 \in Node |-> [ledger[n2] EXCEPT ![lastHash'] = [kind |-> "receive", amount |-> 1, chainId |-> balanceCache[pk], prev |-> lastHash, recipient |-> NoBlock, sig |-> n]]]
  /\ receivedSet' = [n2 \in Node |-> @ \cup {lastHash'}]
  /\ balanceCache' = balanceCache

CreateChange(n) ==
  /\ lastHash # NoHash
  /\ lastHash' = CalculateHashImpl([kind |-> "change", amount |-> 0, chainId |-> balanceCache[n], prev |-> lastHash, recipient |-> NoBlock], lastHash)
  /\ ledger' = [n2 \in Node |-> [ledger[n2] EXCEPT ![lastHash'] = [kind |-> "change", amount |-> 0, chainId |-> balanceCache[n], prev |-> lastHash, recipient |-> NoBlock, sig |-> n]]]
  /\ receivedSet' = [n2 \in Node |-> @ \cup {lastHash'}]
  /\ balanceCache' = balanceCache

ValidateBlock(n) ==
  /\ \E h \in receivedSet[n] :
       /\ ledger[n][h] = NoBlockVal
       /\ \E nd \in Node : ledger[nd][h] /= NoBlockVal
       /\ ledger' = [ledger EXCEPT ![n][h] = ledger[CHOOSE nd \in Node : ledger[nd][h] /= NoBlockVal][h]]
       /\ receivedSet' = [receivedSet EXCEPT ![n] = @ \ {h}]
  /\ lastHash' = lastHash
  /\ balanceCache' = balanceCache

Next ==
  \/ BeginGenesis
  \/ \E n \in Node : CreateSend(n) \/ CreateOpen(n) \/ CreateReceive(n) \/ CreateChange(n) \/ ValidateBlock(n)

Spec ==
  /\ Init
  /\ [][Next]_vars

SafetyInvariant ==
  /\ TypeOK
  /\ \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].sig \in PrivateKey

====