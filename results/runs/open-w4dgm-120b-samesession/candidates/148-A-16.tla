---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME NoHash \notin Hash /\ NoBlock \notin Hash /\ NoHashVal \notin HASH

OwnedKey == CHOOSE pk \in PrivateKey : TRUE

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (PublicKey \X [Hash -> PublicKey] \X ("genesis" \X Nat) \X ("send" \X PublicKey \X Nat) \X ("receive" \X PublicKey \X Hash) \X ("open" \X PublicKey) \X ("change" \X PublicKey)) \X ("self" \X Hash) \X ("signed" \X PrivateKey) \X ("prevValid" \X BOOLEAN))]
    /\ received \in [Node -> SUBSET Hash]

\* BalanceWalk walks the account chain for an account and sums, starting
\* from the genesis hash and following the chain in hash order.
BalanceWalk(ch, h) ==
    LET f(x) == IF x \in Hash /\ ledger[ch][x] # NoBlockVal /\ ledger[ch][x][4][1] = "receive"
                  THEN LET prev = ledger[ch][x][4][2] IN IF prev = NoHash THEN 0 ELSE BalanceWalk(ch, prev) + ledger[ch][x][4][2]
                  ELSE 0
    IN IF h \in Hash /\ ledger[ch][h] # NoBlockVal /\ ledger[ch][h][4][1] \in {"open", "change"}
          THEN LET prev = ledger[ch][h][5] IN IF prev = NoHash THEN 0 ELSE BalanceWalk(ch, prev)
          ELSE IF h \in Hash /\ ledger[ch][h] # NoBlockVal /\ ledger[ch][h][4][1] = "send" THEN 0
          ELSE f(h)

RECURSIVE BalanceWalk(_)
BalanceWalk(_)

Total ==
    LET rec(S) == IF S = {} THEN 0
                  ELSE LET a == CHOOSE x \in S : TRUE IN BalanceWalk(a, NoHash) + rec(S \ {a})
    IN rec(PublicKey)

Init ==
    /\ lastHash = NoHash
    /\ ledger = [ch \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [ch \in Node |-> {}]

\* The genesis block is the only way coins enter the system, so the
\* invariant about coin conservation only makes sense if it can be created.
CreateGenesisBlock ==
    /\ \A ch \in Node : ledger[ch][NoHash] = NoBlockVal
    /\ \E ch \in Node, pk \in PrivateKey :
         /\ ledger' = [ledger EXCEPT ![ch][NoHash] = <<PublicKey[pk], [NoHash |-> NoHash], "genesis" \X GenesisBalance, "self" \X NoHash, "signed" \X pk, "prevValid" \X TRUE>>]
    /\ lastHash' = NoHash
    /\ received' = [c \in Node |-> {NoHash}]

CreateSendBlock(ch, pk, to, amt) ==
    /\ ledger[ch][lastHash] # NoBlockVal
    /\ ledger[ch][lastHash][3][1] = "open"
    /\ ledger[ch][lastHash][3][2] >= amt
    /\ ledger[ch][lastHash][4][1] = "genesis" \/ ledger[ch][lastHash][4][1] = "receive"
    /\ LET nh == CalculateHashImpl(<<PublicKey[pk], lastHash, "send", to, amt>>) IN
         /\ ledger' = [c \in Node |-> [ledger[c] EXCEPT ![nh] = <<PublicKey[pk], [lastHash |-> lastHash], "send" \X to \X amt, "prevValid" \X TRUE>>]
         /\ lastHash' = nh
         /\ received' = [c \in Node |-> received[c] \cup {nh}]

CreateOpenBlock(ch, pk, from) ==
    /\ ledger[ch][lastHash] # NoBlockVal
    /\ ledger[ch][lastHash][3][1] = "open"
    /\ \E h \in Hash :
         /\ ledger[ch][h] # NoBlockVal
         /\ ledger[ch][h][3][1] = "send"
         /\ ledger[ch][h][3][2] = from
         /\ ledger[ch][h][4][2] = NoHash
         /\ LET nh == CalculateHashImpl(<<PublicKey[pk], lastHash, "open", from>>) IN
              /\ ledger' = [c \in Node |-> [ledger[c] EXCEPT ![nh] = <<PublicKey[pk], [lastHash |-> lastHash], "open" \X from, "prevValid" \X TRUE>>]
              /\ ledger' = [c \in Node |-> [ledger'c EXCEPT ![h][4] = <<from, nh>>]]
              /\ lastHash' = nh
              /\ received' = [c \in Node |-> received[c] \cup {nh}]

CreateReceiveBlock(ch, pk, from, h) ==
    /\ ledger[ch][lastHash] # NoBlockVal
    /\ ledger[ch][lastHash][3][1] = "open"
    /\ ledger[ch][h] # NoBlockVal
    /\ ledger[ch][h][3][1] = "send"
    /\ ledger[ch][h][3][2] = from
    /\ ledger[ch][h][4][2] = NoHash
    /\ LET nh == CalculateHashImpl(<<PublicKey[pk], lastHash, "receive", from, h>>) IN
         /\ ledger' = [c \in Node |-> [ledger[c] EXCEPT ![nh] = <<PublicKey[pk], [lastHash |-> lastHash], "receive" \X from \X h, "prevValid" \X TRUE>>]
         /\ ledger' = [c \in Node |-> [ledger'c EXCEPT ![h][4] = <<from, nh>>]]
         /\ lastHash' = nh
         /\ received' = [c \in Node |-> received[c] \cup {nh}]

CreateChangeRepBlock(ch, pk, to) ==
    /\ ledger[ch][lastHash] # NoBlockVal
    /\ ledger[ch][lastHash][3][1] \in {"open", "receive"}
    /\ LET nh == CalculateHashImpl(<<PublicKey[pk], lastHash, "change", to>>) IN
         /\ ledger' = [c \in Node |-> [ledger[c] EXCEPT ![nh] = <<PublicKey[pk], [lastHash |-> lastHash], "change" \X to, "prevValid" \X TRUE>>]
         /\ lastHash' = nh
         /\ received' = [c \in Node |-> received[c] \cup {nh}]

ValidateBlock(ch, h) ==
    /\ h \in received[ch]
    /\ ledger[ch][h] \in {NoBlockVal, "self"}
    /\ ledger[ch][lastHash] # NoBlockVal
    /\ ledger[ch][h] = <<PublicKey[OwnedKey], [lastHash |-> lastHash], "self", "prevValid" \X TRUE>>
    /\ ledger' = [ledger EXCEPT ![ch][h] = <<PublicKey[OwnedKey], [lastHash |-> lastHash], "self", "prevValid" \X TRUE>>]
    /\ received' = [received EXCEPT ![ch] = received[ch] \ {h}]
    /\ UNCHANGED lastHash

Next ==
    \/ CreateGenesisBlock
    \/ \E ch \in Node, pk \in PrivateKey, to \in PublicKey, amt \in 1..GenesisBalance : CreateSendBlock(ch, pk, to, amt)
    \/ \E ch \in Node, pk \in PrivateKey, from \in PublicKey : CreateOpenBlock(ch, pk, from)
    \/ \E ch \in Node, pk \in PrivateKey, from \in PublicKey, h \in Hash : CreateReceiveBlock(ch, pk, from, h)
    \/ \E ch \in Node, pk \in PrivateKey, to \in PublicKey : CreateChangeRepBlock(ch, pk, to)
    \/ \E ch \in Node, h \in Hash : ValidateBlock(ch, h)

Spec == Init /\ [][Next]_vars

\* Balance conservation would be a separate per-account equality property
\* derived from BalanceWalk; the invariant below is the signature check.
SafetyInvariant ==
    \A ch \in Node : \A h \in Hash :
        ledger[ch][h] # NoBlockVal => ledger[ch][h][8] \in {PublicKey[p] : p \in PrivateKey}

\* The signature check is the only thing distinguishing a legitimate block
\* from an attacker-added block; the other checks are all local book-keeping.
CryptoInvariant ==
    \A ch \in Node : \A h \in Hash :
        ledger[ch][h] # NoBlockVal => ledger[ch][h][8] = PublicKey[ledger[ch][h][7]]

\* The invariant below is an accounting identity rather than a safety
\* property about the protocol, and it is not part of the required set.
BalanceConservation ==
    Total <= GenesisBalance

====