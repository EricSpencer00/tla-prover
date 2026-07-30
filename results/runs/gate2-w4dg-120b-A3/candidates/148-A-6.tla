---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME NoHashVal \notin Hash
ASSUME NoBlockVal \notin Hash
ASSUME NoHash \notin Hash
ASSUME NoBlock \notin Hash
ASSUME GenesisBalance \in Nat

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* A signed block carries its own hash (derived from its data), the
\* chain it belongs to (the owner's public key), the previous block in
\* that chain, an optional sender reference, the block type, and the
\* Ed25519 signature over the owner key and block hash.
SignedBlock == [hash: Hash, ownerPk: PublicKey, prev: Hash,
                 senderRef: Hash, kind: {"genesis", "send", "open", "receive", "changeRep"},
                 sig: [key: PrivateKey, msg: Hash]]

ACCOUNT == {b \in Hash : ledger[NoHash][b].kind # "send"}

TypeOK ==
  /\ lastHash \in (Hash \cup {NoHashVal})
  /\ ledger \in [Hash -> [Hash -> SignedBlock \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> [g \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

SignatureValid(bl) ==
  let k == ledger[NoHash][bl.ownerPk].prev in
    ledger[NoHash][k].hash = bl.senderRef /\ bl.sig.key = k /\ bl.sig.msg = bl.hash

\* The ledger maps hashes to blocks, but blocks are retrieved by the
\* public key of the chain they belong to. The empty ledger keeps the
\* mapping at hash NoHash but still maps every hash to NoBlockVal.
OpenOwner(s) == IF s = NoBlockVal THEN NoHash ELSE s.ownerPk

\* Balance is computed from the account chain by folding backwards from
\* the latest block, ignoring the genesis block (which had the full
\* supply) so that its effect is not counted as a spend.
RECURSIVE ChainBalance(_)
ChainBalance(s) ==
  IF s = NoBlockVal THEN 0
  ELSE IF s.kind = "genesis" THEN 0
  ELSE IF s.kind = "send" THEN ChainBalance(ledger[OpenOwner(s.prev)][s.prev])
  ELSE IF s.kind \in {"open", "receive"}
         THEN ChainBalance(ledger[OpenOwner(s.prev)][s.prev]) + 1
  ELSE ChainBalance(ledger[OpenOwner(s.prev)][s.prev])

RECURSIVE SumBalances(_)
SumBalances(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN ChainBalance(ledger[NoHash][x]) + SumBalances(S \ {x})

TypeInvariant == TypeOK

\* The invariant groups every block per account chain (rather than in a
\* single flat pool) to keep the signature check short enough to be
\* evaluated in a bounded model, while still covering the whole ledger.
SafetyInvariant ==
  /\ lastHash \in (Hash \cup {NoHashVal})
  /\ \A s \in ACCOUNT : SignatureValid(s)

\* Every action below adds the block it created to every node's received
\* set, so a flooded network always has the broadcast waiting to be
\* validated; the validate action then folds it into each node's copy.

CreateGenesis ==
  /\ lastHash = NoHashVal
  /\ \A k \in PrivateKey :
       \E newH \in Hash :
         /\ ledger[NoHash][newH] = [hash |-> newH, ownerPk |-> PrivateKey, prev |-> NoHash,
                                    senderRef |-> NoHash, kind |-> "genesis",
                                    sig |-> [key |-> k, msg |-> newH]]
         /\ lastHash' = newH
  /\ ledger' = [h \in Hash |-> [g \in Hash |-
        {NoBlockVal} |-> IF g = NoBlockVal THEN NoBlockVal
                            ELSE ledger[NoHash][g]]
                 EXCEPT ![newH] = ledger[NoHash][newH]]
  /\ received' = [n \in Node |-> received[n] \cup {newH}]

CreateSend(n, outFk) ==
  /\ \E s \in ACCOUNT :
       s.kind \notin {"send", "receive"}
       /\ ChainBalance(s) > 0
       /\ \E newH \in Hash :
            /\ ledger[NoHash][newH] = [hash |-> newH, ownerPk |-> outFk, prev |-> s.hash,
                                       senderRef |-> NoHash, kind |-> "send",
                                       sig |-> [key |-> outFk, msg |-> newH]]
            /\ lastHash' = newH
            /\ ledger' = [h \in Hash |-> [g \in Hash |-
                 {NoBlockVal} |-> IF g = NoBlockVal THEN NoBlockVal
                                     ELSE ledger[NoHash][g]]
                 EXCEPT ![newH] = ledger[NoHash][newH]]
            /\ received' = [m \in Node |-> received[m] \cup {newH}]

\* An open block starts a new account chain for the recipient.
CreateOpen(n, inFk) ==
  /\ \E s \in ACCOUNT :
       s.kind \notin {"open", "receive"}
       /\ s.kind = "send"
       /\ ChainBalance(s) > 0
       /\ s.ownerPk = inFk
       /\ \E newH \in Hash :
            /\ ledger[NoHash][newH] = [hash |-> newH, ownerPk |-> inFk, prev |-> NoHash,
                                       senderRef |-> s.hash, kind |-> "open",
                                       sig |-> [key |-> inFk, msg |-> newH]]
            /\ lastHash' = newH
            /\ ledger' = [h \in Hash |-> [g \in Hash |-
                 {NoBlockVal} |-> IF g = NoBlockVal THEN NoBlockVal
                                     ELSE ledger[NoHash][g]]
                 EXCEPT ![newH] = ledger[NoHash][newH]]
            /\ received' = [m \in Node |-> received[m] \cup {newH}]

CreateReceive(n) ==
  /\ \E s \in ACCOUNT :
       s.kind = "send"
       /\ ChainBalance(s) > 0
       /\ \E r \in ACCOUNT :
            r.kind \notin {"receive", "send"}
            /\ r.ownerPk = s.ownerPk
            /\ \E newH \in Hash :
                 /\ ledger[NoHash][newH] = [hash |-> newH, ownerPk |-> r.ownerPk,
                                            prev |-> r.hash, senderRef |-> s.hash,
                                            kind |-> "receive",
                                            sig |-> [key |-> r.ownerPk, msg |-> newH]]
                 /\ lastHash' = newH
                 /\ ledger' = [h \in Hash |-> [g \in Hash |-
                      {NoBlockVal} |-> IF g = NoBlockVal THEN NoBlockVal
                                      ELSE ledger[NoHash][g]]
                      EXCEPT ![newH] = ledger[NoHash][newH]]
                 /\ received' = [m \in Node |-> received[m] \cup {newH}]

CreateChangeRep(n, repFk) ==
  /\ \E s \in ACCOUNT :
       s.kind \notin {"send", "receive"}
       /\ ChainBalance(s) > 0
       /\ repFk # s.ownerPk
       /\ \E newH \in Hash :
            /\ ledger[NoHash][newH] = [hash |-> newH, ownerPk |-> repFk, prev |-> s.hash,
                                       senderRef |-> NoHash, kind |-> "changeRep",
                                       sig |-> [key |-> repFk, msg |-> newH]]
            /\ lastHash' = newH
            /\ ledger' = [h \in Hash |-> [g \in Hash |-
                 {NoBlockVal} |-> IF g = NoBlockVal THEN NoBlockVal
                                     ELSE ledger[NoHash][g]]
                 EXCEPT ![newH] = ledger[NoHash][newH]]
            /\ received' = [m \in Node |-> received[m] \cup {newH}]

ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[NoHash][h] # NoBlockVal
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[NoHash][h]]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node, outFk \in PrivateKey : CreateSend(n, outFk)
  \/ \E n \in Node, inFk \in PrivateKey : CreateOpen(n, inFk)
  \/ \E n \in Node : CreateReceive(n)
  \/ \E n \in Node, repFk \in PrivateKey : CreateChangeRep(n, repFk)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)
  \/ CreateGenesis

Spec == Init /\ [][Next]_vars

====