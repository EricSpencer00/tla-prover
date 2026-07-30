---- MODULE Nano ----
EXTENDS Naturals, Sequences

CONSTANTS
  Hash, NoHashVal,
  PrivateKey, PublicKey,
  Node, GenesisBalance,
  NoBlockVal,
  CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, recvSet

vars == <<lastHash, ledger, recvSet>>

\* Block types record the natural ordering of actions, and their recursive
\* balance functions walk the account chain exactly in that order.
\* calculateHash is swapped out by the .cfg (CalculateHashImpl) at model time.
TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> [pubKey: PublicKey, hash: Hash, prev: Hash \cup {NoHash}, kind: {"genesis", "send", "open", "receive", "change"}, amount: 0..GenesisBalance, target: PublicKey]]]
  /\ recvSet \subseteq [node: Node, hash: Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ recvSet = {}

\* Balance walks the chain starting from a leaf hash backwards to genesis.
Balance(n, h) ==
  LET sumSeq(m, seq) ==
        IF m = <<>> THEN 0
        ELSE LET blk = ledger[n][Head(m)]
             IN IF blk.kind = "send" THEN sumSeq(Tail(m), seq) - blk.amount
                ELSE IF blk.kind = "receive" THEN sumSeq(Tail(m), seq) + blk.amount
                ELSE 0
  IN sumSeq(Append(seq, h), seq)

\* The invariant is separate from the type one because self-enforced balance
\* limits are a stricter conservation discipline, not just a type check.
BalanceConserved ==
  LET nodeBalances == {Balance(n, h) : n \in Node, h \in Hash, ledger[n][h] # NoBlockVal}
     sumBal(s) == IF s = {} THEN 0 ELSE LET x == CHOOSE y \in s : TRUE IN x + sumBal(s \ {x})
  IN sumBal(nodeBalances) <= GenesisBalance

\* Signature checks are the only real security rule: a node must not add a
\* block to its ledger that it cannot cryptographically justify.
CryptographicSoundness ==
  \A n \in Node, h \in Hash :
    (ledger[n][h] # NoBlockVal) => (ledger[n][h].pubKey = (CHOOSE pk \in PublicKey : PKtoKey[pk] = ledger[n][h].pubKey))

\* The model always has a pending block to add, since a finite hash space
\* is saturated: each create action overwrites lastHash and cannot repeat.
CreateGenesis ==
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash(NoHash, NoHashVal)
  /\ \A n \in Node :
       /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [pubKey |-> PKtoKey[CHOOSE n \in Node : TRUE], hash |-> lastHash', prev |-> NoHash, kind |-> "genesis", amount |-> GenesisBalance, target |-> NoBlock]]
       /\ recvSet' = recvSet \cup {[node |-> n, hash |-> lastHash']}
  /\ UNCHANGED <<nodeBalances>>

\* New blocks are broadcast to every other node before they may be written,
\* so the ordering observed at each node may differ, which is the whole point.
CreateSend(n) ==
  /\ lastHash # NoHashVal
  /\ Balance(n, lastHash) > 0
  /\ lastHash' = CalculateHash(lastHash, NoHashVal)
  /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [pubKey |-> PKtoKey[n], hash |-> lastHash', prev |-> lastHash, kind |-> "send", amount |-> 1, target |-> NoBlock]]
  /\ recvSet' = recvSet \cup {[node |-> m, hash |-> lastHash'] : m \in Node}
  /\ UNCHANGED <<nodeBalances>>

\* The open block is what makes a cold account live without prior balance.
CreateOpen(n, m) ==
  /\ ledger[n][lastHash] # NoBlockVal
  /\ ledger[n][lastHash].prev = NoHash
  /\ ledger[n][lastHash].kind = "send"
  /\ ledger[n][lastHash].target = PKtoKey[m]
  /\ lastHash' = CalculateHash(lastHash, NoHashVal)
  /\ ledger' = [ledger EXCEPT ![m][lastHash'] = [pubKey |-> PKtoKey[m], hash |-> lastHash', prev |-> NoHash, kind |-> "open", amount |-> 0, target |-> NoBlock]]
  /\ recvSet' = recvSet \cup {[node |-> x, hash |-> lastHash'] : x \in Node}
  /\ UNCHANGED <<nodeBalances>>

CreateReceive(n, m) ==
  /\ ledger[m][lastHash] # NoBlockVal
  /\ ledger[m][lastHash].prev = NoHash
  /\ ledger[m][lastHash].kind = "send"
  /\ ledger[m][lastHash].target = PKtoKey[n]
  /\ lastHash' = CalculateHash(lastHash, NoHashVal)
  /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [pubKey |-> PKtoKey[n], hash |-> lastHash', prev |-> NoHash, kind |-> "receive", amount |-> ledger[m][lastHash].amount, target |-> NoBlock]]
  /\ recvSet' = recvSet \cup {[node |-> x, hash |-> lastHash'] : x \in Node}
  /\ UNCHANGED <<nodeBalances>>

CreateChangeRep(n) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash(lastHash, NoHashVal)
  /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [pubKey |-> PKtoKey[n], hash |-> lastHash', prev |-> lastHash, kind |-> "change", amount |-> 0, target |-> NoBlock]]
  /\ recvSet' = recvSet \cup {[node |-> x, hash |-> lastHash'] : x \in Node}
  /\ UNCHANGED <<nodeBalances>>

ProcessAddBlock(c) ==
  /\ c \in recvSet
  /\ recvSet' = recvSet \ {c}
  /\ ledger' = [ledger EXCEPT ![c.node][c.hash] = [pubKey |-> PKtoKey[c.node], hash |-> c.hash, prev |-> NoHash, kind |-> "genesis", amount |-> GenesisBalance, target |-> NoBlock]]
  /\ UNCHANGED <<lastHash, nodeBalances>>

Next ==
  \/ CreateGenesis
  \/ \E n \in Node : CreateSend(n)
  \/ \E n, m \in Node : CreateOpen(n, m)
  \/ \E n, m \in Node : CreateReceive(n, m)
  \/ \E n \in Node : CreateChangeRep(n)
  \/ \E c \in recvSet : ProcessAddBlock(c)

Spec == Init /\ [][Next]_vars

TypeInvariant == TypeOK /\ BalanceConserved
SafetyInvariant == CryptographicSoundness

====