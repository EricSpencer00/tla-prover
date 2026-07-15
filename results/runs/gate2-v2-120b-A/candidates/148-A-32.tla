---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------------
  Constants (as required by the .cfg)
-----------------------------------------------------------------------*)
CONSTANTS
    Hash,               \* the set of all possible block hashes
    NoHashVal,          \* a distinguished sentinel for “no hash”
    PrivateKey,         \* the set of private keys
    PublicKey,          \* the set of public keys
    Node,               \* the set of network nodes
    GenesisBalance,     \* the total supply of coins (a natural number)
    NoBlockVal,         \* sentinel representing “no block”
    CalculateHash,      \* abstract hash‑calculation operator
    NoHash,             \* synonym for the sentinel hash (for readability)
    NoBlock             \* synonym for the sentinel block (for readability)

(*-----------------------------------------------------------------------
  Types
-----------------------------------------------------------------------*)
BlockType == {"Genesis", "Send", "Open", "Receive", "Change"}

Block == [
    type          : BlockType,
    hash          : Hash,
    prev          : (Hash \cup {NoHashVal}),
    account       : PublicKey,
    balance       : Nat,
    amount        : Nat,
    destination   : (PublicKey \cup {NoHashVal}),
    source        : (Hash \cup {NoHashVal}),
    representative: (PublicKey \cup {NoHashVal}),
    signature     : PubKeySig   \* see definition below
]

PubKeySig == [pk : PublicKey, s : {0,1} ]   \* abstract signature (key + bit)

\* All possible blocks, including the sentinel
AllBlocks == { NoBlock } \cup Block

(*-----------------------------------------------------------------------
  State variables
-----------------------------------------------------------------------*)
VARIABLES
    lastHash,          \* the most recent block hash (or NoHashVal)
    ledgers,           \* [node \in Node -> [h \in Hash -> Block \cup {NoBlock}]]
    received           \* [node \in Node -> SUBSET Hash]   (hashes in transit)

(*-----------------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------------*)
LedgerOf(node) == ledgers[node]

\* Balance of an account is obtained by traversing its chain from the
\* most recent block back to the genesis/open block.
AccountBalance(node, acc) ==
    LET chain == CHOOSE b \in AllBlocks :
                    /\ b = NoBlock
                    \/ /\ b.account = acc
                       /\ b.hash \in DOMAIN LedgerOf(node)
    IN
        IF chain = NoBlock THEN 0
        ELSE ChainBalance(node, chain)

\* Recursive walk of a chain to compute balance
ChainBalance(node, b) ==
    IF b.type = "Genesis" THEN b.balance
    ELSE IF b.type = "Open"   THEN b.balance
    ELSE IF b.type = "Send"   THEN ChainBalance(node, LedgerOf(node)[b.prev]) - b.amount
    ELSE IF b.type = "Receive" THEN ChainBalance(node, LedgerOf(node)[b.prev]) + b.amount
    ELSE IF b.type = "Change" THEN ChainBalance(node, LedgerOf(node)[b.prev])
    ELSE 0

\* Verify that a signature matches the public key of the block’s account.
ValidSignature(b) ==
    /\ b.signature.pk = b.account
    /\ b.signature.s \in {0,1}        \* abstract check; real crypto omitted

\* Sum of all balances across all nodes (used only in comments, not an invariant)
TotalBalance == 
    LET balances == { AccountBalance(node, acc) :
                        node \in Node, acc \in PublicKey }
    IN  Sum(balances)

(*-----------------------------------------------------------------------
  Initial predicate
-----------------------------------------------------------------------*)
Init ==
    /\ lastHash = NoHashVal
    /\ ledgers = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

(*-----------------------------------------------------------------------
  Actions
-----------------------------------------------------------------------*)
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E pk \in PublicKey :
        LET b ==
            [type          |-> "Genesis",
             hash          |-> CalculateHash(["Genesis"], NoHashVal),
             prev          |-> NoHashVal,
             account       |-> pk,
             balance       |-> GenesisBalance,
             amount        |-> 0,
             destination   |-> NoHashVal,
             source        |-> NoHashVal,
             representative|-> NoHashVal,
             signature     |-> [pk |-> pk, s |-> 0]]
        /\ b.hash = lastHash'      \* lastHash' will be assigned below
        /\ lastHash' = b.hash
        /\ \A n \in Node :
              /\ ledgers' = [ledgers EXCEPT ![n] = [@ EXCEPT ![b.hash] = b]]
              /\ received' = [received EXCEPT ![n] = {}]

CreateSend(node) ==
    /\ node \in Node
    /\ \E senderKey \in PrivateKey :
        /\ PublicKeyOf(senderKey) = acc
        /\ acc \in PublicKey
        /\ let prevHash == 
               CHOOSE h \in Hash : ledgers[node][h] # NoBlock /\ 
                                   ledgers[node][h].account = acc /\
                                   ledgers[node][h].type # "Send" \/ TRUE
           in 
        /\ let prevBlock == ledgers[node][prevHash] in
        /\ AccountBalance(node, acc) >= amt
        /\ amt \in Nat
        /\ dest \in PublicKey
        /\ let newHash == CalculateHash([senderKey, prevHash, amt, dest], lastHash) in
        /\ let newBlock ==
               [type          |-> "Send",
                hash          |-> newHash,
                prev          |-> prevHash,
                account       |-> acc,
                balance       |-> AccountBalance(node, acc),
                amount        |-> amt,
                destination   |-> dest,
                source        |-> NoHashVal,
                representative|-> NoHashVal,
                signature     |-> [pk |-> senderKey, s |-> 0]]
           in
        /\ lastHash' = newHash
        /\ \A n \in Node :
              /\ ledgers' = [ledgers EXCEPT ![n] = [@ EXCEPT ![newHash] = newBlock]]
              /\ received' = [received EXCEPT ![n] = @ \cup {newHash}]

CreateOpen(node, sendHash) ==
    /\ node \in Node
    /\ sendHash \in Hash
    /\ sentBlk == ledgers[node][sendHash]
    /\ sentBlk.type = "Send"
    /\ sentBlk.destination = PublicKeyOf(NodeOwnerKey(node))
    /\ \E openBlk \in AllBlocks :
        /\ openBlk.type = "Open"
        /\ openBlk.account = sentBlk.destination
        /\ openBlk.source = sendHash
        /\ openBlk.balance = sentBlk.amount
        /\ openBlk.prev = NoHashVal
        /\ openBlk.signature.pk = openBlk.account
        /\ openBlk.signature.s \in {0,1}
        /\ let newHash == CalculateHash([openBlk], lastHash) in
        /\ newHash = openBlk.hash
        /\ lastHash' = newHash
        /\ \A n \in Node :
              /\ ledgers' = [ledgers EXCEPT ![n] = [@ EXCEPT ![newHash] = openBlk]]
              /\ received' = [received EXCEPT ![n] = @ \cup {newHash}]

CreateReceive(node, sendHash) ==
    /\ node \in Node
    /\ sendHash \in Hash
    /\ sentBlk == ledgers[node][sendHash]
    /\ sentBlk.type = "Send"
    /\ sentBlk.destination = PublicKeyOf(NodeOwnerKey(node))
    /\ \E prevHash \in Hash :
        /\ prevBlk == ledgers[node][prevHash]
        /\ prevBlk.account = sentBlk.destination
        /\ prevBlk.type \in {"Open", "Receive", "Change"}
        /\ let newHash == CalculateHash([prevHash, sendHash], lastHash) in
        /\ let recvBlk ==
               [type          |-> "Receive",
                hash          |-> newHash,
                prev          |-> prevHash,
                account       |-> sentBlk.destination,
                balance       |-> AccountBalance(node, sentBlk.destination) + sentBlk.amount,
                amount        |-> sentBlk.amount,
                destination   |-> NoHashVal,
                source        |-> sendHash,
                representative|-> NoHashVal,
                signature     |-> [pk |-> sentBlk.destination, s |-> 0]]
           in
        /\ lastHash' = newHash
        /\ \A n \in Node :
              /\ ledgers' = [ledgers EXCEPT ![n] = [@ EXCEPT ![newHash] = recvBlk]]
              /\ received' = [received EXCEPT ![n] = @ \cup {newHash}]

CreateChange(node) ==
    /\ node \in Node
    /\ let pk == PublicKeyOf(NodeOwnerKey(node)) in
    /\ \E prevHash \in Hash :
        /\ prevBlk == ledgers[node][prevHash]
        /\ prevBlk.account = pk
        /\ let newHash == CalculateHash([prevHash, pk], lastHash) in
        /\ let chgBlk ==
               [type          |-> "Change",
                hash          |-> newHash,
                prev          |-> prevHash,
                account       |-> pk,
                balance       |-> prevBlk.balance,
                amount        |-> 0,
                destination   |-> NoHashVal,
                source        |-> NoHashVal,
                representative|-> pk,
                signature     |-> [pk |-> pk, s |-> 0]]
           in
        /\ lastHash' = newHash
        /\ \A n \in Node :
              /\ ledgers' = [ledgers EXCEPT ![n] = [@ EXCEPT ![newHash] = chgBlk]]
              /\ received' = [received EXCEPT ![n] = @ \cup {newHash}]

ProcessReceived(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
        LET blk == ledgers[node][h] IN
        /\ blk # NoBlock
        /\ ValidSignature(blk)
        /\ (blk.type = "Send" => 
                /\ blk.account \in PublicKey
                /\ blk.amount \in Nat
                /\ blk.destination \in PublicKey
                /\ AccountBalance(node, blk.account) >= blk.amount)
        /\ (blk.type = "Open" => 
                /\ blk.source \in Hash
                /\ ledgers[node][blk.source].type = "Send"
                /\ ledgers[node][blk.source].destination = blk.account)
        /\ (blk.type = "Receive" => 
                /\ blk.source \in Hash
                /\ ledgers[node][blk.source].type = "Send"
                /\ ledgers[node][blk.source].destination = blk.account)
        /\ (blk.type = "Change" => TRUE)
        /\ \A n \in Node :
              /\ ledgers' = [ledgers EXCEPT ![n] = @]      \* ledger already contains blk
              /\ received' = [received EXCEPT ![node] = @ \ {h}]

Next ==
    \/ CreateGenesis
    \/ \E n \in Node : CreateSend(n)
    \/ \E n \in Node, h \in Hash : CreateOpen(n, h)
    \/ \E n \in Node, h \in Hash : CreateReceive(n, h)
    \/ \E n \in Node : CreateChange(n)
    \/ \E n \in Node : ProcessReceived(n)

Spec == Init /\ [][Next]_<<lastHash, ledgers, received>>

(*-----------------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------------*)
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledgers \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

(*-----------------------------------------------------------------------
  Safety invariant (cryptographic correctness)
-----------------------------------------------------------------------*)
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET blk == ledgers[n][h] IN
            blk = NoBlock \/ ValidSignature(blk)

=============================================================================