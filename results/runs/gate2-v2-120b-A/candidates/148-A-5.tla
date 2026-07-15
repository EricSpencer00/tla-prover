---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(*  Constants (to be instantiated in the .cfg file)                        *)
(***************************************************************************)
CONSTANTS
    Hash,               \* The set of all possible block hashes
    NoHashVal,          \* A distinguished value meaning "no hash yet"
    PrivateKey,         \* The set of private keys
    PublicKey,          \* The set of public keys
    Node,               \* The set of network nodes
    GenesisBalance,     \* Total number of coins initially created
    NoBlockVal,         \* A distinguished value meaning "no block"
    CalculateHash,      \* Abstract hash operator: [data, prevHash] -> Hash
    NoHash,             \* Alias for NoHashVal (for readability)
    NoBlock,            \* Alias for NoBlockVal
    PrivToPub           \* Mapping from private to public keys

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
BlockType == {"genesis", "send", "open", "receive", "change"}

Block ==
    [type      : BlockType,
     sender    : PublicKey,
     receiver  : PublicKey,
     amount    : Nat,
     prevHash  : Hash,
     hash      : Hash,
     signature : PrivateKey]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A block is well‑typed if its fields are drawn from the correct domains.
BlockWellTyped(b) ==
    /\ b.type \in BlockType
    /\ b.sender \in PublicKey
    /\ b.receiver \in PublicKey
    /\ b.amount \in Nat
    /\ b.prevHash \in Hash
    /\ b.hash \in Hash
    /\ b.signature \in PrivateKey

\* Signature check (abstract, relies on a correct mapping in the .cfg)
SigOK(b) ==
    /\ b.signature \in PrivateKey
    /\ PrivToPub[b.signature] = b.sender

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,   \* the hash of the most recent block in the global order
    ledger,    \* [node \in Node |-> [h \in Hash |-> NoBlock]]
    received   \* [node \in Node |-> {}]

(***************************************************************************)
(*  Initial state                                                         *)
(***************************************************************************)
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

(***************************************************************************)
(*  Block creation actions                                                *)
(***************************************************************************)

CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \A n \in Node: ledger[n][NoHashVal] = NoBlock
    /\ LET gBlock ==
            [type      |-> "genesis",
             sender    |-> PrivToPub[CHOOSE k \in PrivateKey : TRUE],
             receiver  |-> PrivToPub[CHOOSE k \in PrivateKey : TRUE],
             amount    |-> GenesisBalance,
             prevHash  |-> NoHashVal,
             hash      |-> CalculateHash([type |-> "genesis",
                                         sender |-> PrivToPub[CHOOSE k \in PrivateKey : TRUE],
                                         receiver |-> PrivToPub[CHOOSE k \in PrivateKey : TRUE],
                                         amount |-> GenesisBalance,
                                         prevHash |-> NoHashVal], NoHashVal),
             signature |-> CHOOSE k \in PrivateKey : PrivToPub[k] = PrivToPub[CHOOSE k' \in PrivateKey : TRUE]]
         IN
       /\ lastHash' = gBlock.hash
       /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = gBlock.hash THEN gBlock ELSE ledger[n][h]]]
       /\ received' = [n \in Node |-> {}]
       /\ UNCHANGED << >>

\* Helper to pick a block by hash from a node's ledger
BlockByHash(node, h) == ledger[node][h]

CreateSend(toNode) ==
    /\ toNode \in Node
    /\ \E senderNode \in Node:
        \E prevHash \in Hash:
            LET senderAcc == PrivToPub[CHOOSE k \in PrivateKey : TRUE] IN
            LET sndBlock ==
                [type      |-> "send",
                 sender    |-> senderAcc,
                 receiver  |-> PrivToPub[CHOOSE k \in PrivateKey : TRUE],
                 amount    |-> 1,   \* for simplicity we always send 1 coin
                 prevHash  |-> prevHash,
                 hash      |-> CalculateHash([type |-> "send",
                                             sender |-> senderAcc,
                                             receiver |-> PrivToPub[CHOOSE k \in PrivateKey : TRUE],
                                             amount |-> 1,
                                             prevHash |-> prevHash], prevHash),
                 signature |-> CHOOSE k \in PrivateKey : PrivToPub[k] = senderAcc]
            IN
            /\ SigOK(sndBlock)
            /\ ledger[senderNode][prevHash] # NoBlock   \* previous block exists
            /\ (Balance(senderNode, prevHash) >= sndBlock.amount)  \* no overdraft
            /\ lastHash' = sndBlock.hash
            /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = sndBlock.hash THEN sndBlock ELSE ledger[n][h]]]
            /\ received' = [n \in Node |-> received[n] \cup {sndBlock}]
            /\ UNCHANGED lastHash

CreateOpen ==
    /\ \E recvNode \in Node:
        \E sendHash \in Hash:
            LET recvAcc == PrivToPub[CHOOSE k \in PrivateKey : TRUE] IN
            LET openBlock ==
                [type      |-> "open",
                 sender    |-> recvAcc,
                 receiver  |-> recvAcc,
                 amount    |-> 0,
                 prevHash  |-> sendHash,
                 hash      |-> CalculateHash([type |-> "open",
                                             sender |-> recvAcc,
                                             receiver |-> recvAcc,
                                             amount |-> 0,
                                             prevHash |-> sendHash], sendHash),
                 signature |-> CHOOSE k \in PrivateKey : PrivToPub[k] = recvAcc]
            IN
            /\ ledger[recvNode][sendHash] # NoBlock
            /\ ledger[recvNode][openBlock.prevHash].type = "send"
            /\ ledger[recvNode][openBlock.prevHash].receiver = recvAcc
            /\ SigOK(openBlock)
            /\ lastHash' = openBlock.hash
            /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = openBlock.hash THEN openBlock ELSE ledger[n][h]]]
            /\ received' = [n \in Node |-> received[n] \cup {openBlock}]
            /\ UNCHANGED << >>

CreateReceive ==
    /\ \E recvNode \in Node:
        \E prevHash \in Hash:
            \E sendHash \in Hash:
                LET recvAcc == PrivToPub[CHOOSE k \in PrivateKey : TRUE] IN
                LET recvBlock ==
                    [type      |-> "receive",
                     sender    |-> recvAcc,
                     receiver  |-> recvAcc,
                     amount    |-> 1,
                     prevHash  |-> prevHash,
                     hash      |-> CalculateHash([type |-> "receive",
                                                 sender |-> recvAcc,
                                                 receiver |-> recvAcc,
                                                 amount |-> 1,
                                                 prevHash |-> prevHash,
                                                 sendHash |-> sendHash], prevHash),
                     signature |-> CHOOSE k \in PrivateKey : PrivToPub[k] = recvAcc]
                IN
                /\ ledger[recvNode][prevHash] # NoBlock
                /\ ledger[recvNode][sendHash].type = "send"
                /\ ledger[recvNode][sendHash].receiver = recvAcc
                /\ SigOK(recvBlock)
                /\ lastHash' = recvBlock.hash
                /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = recvBlock.hash THEN recvBlock ELSE ledger[n][h]]]
                /\ received' = [n \in Node |-> received[n] \cup {recvBlock}]
                /\ UNCHANGED << >>

CreateChangeRep ==
    /\ \E node \in Node:
        \E prevHash \in Hash:
            LET repAcc == PrivToPub[CHOOSE k \in PrivateKey : TRUE] IN
            LET chgBlock ==
                [type      |-> "change",
                 sender    |-> repAcc,
                 receiver  |-> repAcc,
                 amount    |-> 0,
                 prevHash  |-> prevHash,
                 hash      |-> CalculateHash([type |-> "change",
                                             sender |-> repAcc,
                                             receiver |-> repAcc,
                                             amount |-> 0,
                                             prevHash |-> prevHash], prevHash),
                 signature |-> CHOOSE k \in PrivateKey : PrivToPub[k] = repAcc]
            IN
            /\ ledger[node][prevHash] # NoBlock
            /\ SigOK(chgBlock)
            /\ lastHash' = chgBlock.hash
            /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = chgBlock.hash THEN chgBlock ELSE ledger[n][h]]]
            /\ received' = [n \in Node |-> received[n] \cup {chgBlock}]
            /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Block processing (validation) action
\* ----------------------------------------------------------------------
ProcessNode(node) ==
    /\ node \in Node
    /\ \E b \in received[node]:
        LET srcNode == CHOOSE n \in Node : b \in received[n] IN
        /\ SigOK(b)
        /\ (b.type = "send" => 
                /\ b.prevHash = NoHashVal \/ ledger[node][b.prevHash] # NoBlock
                /\ b.amount <= Balance(node, b.prevHash))
        /\ (b.type = "receive" =>
                /\ ledger[node][b.prevHash] # NoBlock
                /\ ledger[node][b.receiver] # NoBlock
                /\ ledger[node][b.prevHash].type # "receive")
        /\ (b.type = "open" =>
                /\ ledger[node][b.prevHash] # NoBlock
                /\ ledger[node][b.prevHash].type = "send"
                /\ ledger[node][b.prevHash].receiver = b.receiver)
        /\ (b.type = "change" => ledger[node][b.prevHash] # NoBlock)
        /\ ledger' = [n \in Node |-> 
                        IF n = node 
                        THEN [h \in Hash |-> IF h = b.hash THEN b ELSE ledger[n][h]]
                        ELSE ledger[n]]
        /\ received' = [n \in Node |-> IF n = node THEN received[n] \ {b} ELSE received[n]]
        /\ UNCHANGED lastHash

\* ----------------------------------------------------------------------
\* Global next‑state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ \E to \in Node: CreateSend(to)
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChangeRep
    \/ \E n \in Node: ProcessNode(n)

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

(***************************************************************************)
(*  Invariants                                                             *)
(***************************************************************************)

\* Type invariant – ensures all variables stay within their declared domains
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Block]

\* Safety invariant – every block stored in any ledger has a valid signature
SafetyInvariant ==
    \A n \in Node: \A h \in Hash:
        LET b == ledger[n][h] IN
        b = NoBlock \/ SigOK(b)

\* ----------------------------------------------------------------------
\* Optional auxiliary definitions (not exported)
\* ----------------------------------------------------------------------
Balance(node, h) ==
    IF h = NoHashVal THEN 0
    ELSE
        LET b == ledger[node][h] IN
        IF b = NoBlock THEN 0
        ELSE
            CASE b.type = "genesis" -> b.amount
               [] b.type = "send"    -> Balance(node, b.prevHash) - b.amount
               [] b.type = "receive"-> Balance(node, b.prevHash) + b.amount
               [] b.type = "open"    -> b.amount
               [] b.type = "change"  -> Balance(node, b.prevHash)
               [] OTHER              -> Balance(node, b.prevHash)

=============================================================================