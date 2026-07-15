---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,           \* Finite set of block hashes
    NoHashVal,      \* Sentinel hash value meaning "no previous block"
    PrivateKey,     \* Set of private keys
    PublicKey,      \* Set of public keys
    Node,           \* Set of network nodes
    GenesisBalance, \* Total number of coins at genesis (a natural number)
    NoBlockVal,     \* Sentinel for an absent block
    CalculateHash,  \* Abstract hash function: (prevHash, data) -> Hash
    NoHash,         \* Alias for NoHashVal (for readability)
    NoBlock         \* Alias for NoBlockVal (for readability)

VARIABLES
    lastHash,        \* The most recent block hash known to the system
    ledgers,         \* [node -> [hash -> BlockRecord]]
    receivedSets     \* [node -> SUBSET Hash]

(*-------------------------------------------------------------------*)
(* Block data structures *)
BlockType == {"Genesis", "Send", "Open", "Receive", "ChangeRep"}

BlockRecord == [ 
    type      : BlockType,
    account   : PublicKey,
    balance   : Nat,                 \* Balance after applying this block
    prevHash  : Hash,
    srcPrev   : Hash,                \* For Receive/Open: the referenced send block
    amount    : Nat,                 \* For Send: amount sent; for others 0
    rep       : PublicKey,           \* For ChangeRep: new representative
    sig       : [sk \in PrivateKey |-> BOOLEAN]  \* Abstract signature map
]

(*-------------------------------------------------------------------*)
(* Helper functions *)

\* Given a ledger (a map from hash to BlockRecord) and a hash, compute the balance
\* of the account that owns the chain containing that block.
AccountBalance(ledger, h) ==
    IF h = NoHash THEN 0
    ELSE
        LET blk == ledger[h] IN
        IF blk.type = "Genesis" THEN blk.balance
        ELSE IF blk.type = "Send" THEN blk.balance
        ELSE IF blk.type = "Open" THEN blk.balance
        ELSE IF blk.type = "Receive" THEN blk.balance
        ELSE IF blk.type = "ChangeRep" THEN blk.balance
        ELSE 0

\* Sum of balances of all accounts recorded in a ledger.
TotalBalances(ledger) ==
    \* Enumerate all hashes that start a chain (Genesis or Open) and sum their balances
    LET chainHeads == { h \in Hash : 
            \/ ledger[h].type = "Genesis"
            \/ (ledger[h].type = "Open /\ ledger[h].srcPrev # NoHash) } IN
    Sum({ AccountBalance(ledger, h) : h \in chainHeads })

\* Verify that a signature map contains a single entry for the private key that
\* corresponds to the given public key and that entry is TRUE.
ValidSignature(sigMap, pk) ==
    \E sk \in PrivateKey :
        /\ \A pk2 \in PublicKey : sk # sk => sigMap[sk2] = FALSE
        /\ sigMap[sk] = TRUE
        /\ pk # NoBlockVal => (\A sk2 \in PrivateKey : sigMap[sk2] = FALSE) => TRUE
        /\ \E sk2 \in PrivateKey : pk = ( PUBLICKEYOF[sk2] ) /\ sigMap[sk2] = TRUE

\* Abstract mapping from private to public keys (assumed to be a bijection).
PUBLICKEYOF : [sk \in PrivateKey -> PublicKey]

(*-------------------------------------------------------------------*)
(* Initial state *)

Init ==
    /\ lastHash = NoHash
    /\ ledgers = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ receivedSets = [n \in Node |-> {}]

(*-------------------------------------------------------------------*)
(* Actions *)

CreateGenesis ==
    /\ \E creator \in Node :
        /\ \E pk \in PublicKey :
            /\ \E sk \in PrivateKey :
                /\ PUBLICKEYOF[sk] = pk
                /\ \A n \in Node : ledgers[n][NoHash] = NoBlock
                /\ \A n \in Node : receivedSets[n] = {}
                /\ \A n \in Node :
                    LET blk == [type      |-> "Genesis",
                               account   |-> pk,
                               balance   |-> GenesisBalance,
                               prevHash  |-> NoHash,
                               srcPrev   |-> NoHash,
                               amount    |-> 0,
                               rep       |-> pk,
                               sig       |-> [sk2 \in PrivateKey |-> sk2 = sk]] IN
                    /\ ledgers' = [ledgers EXCEPT ![n][lastHash] = blk]
                /\ lastHash' # NoHash
                /\ \A n \in Node : receivedSets'[n] = {}
    /\ UNCHANGED << >>

CreateSend(sender, amount, recipient) ==
    /\ sender \in Node
    /\ amount \in Nat
    /\ amount <= AccountBalance(ledgers[sender], lastHash)
    /\ \E pk \in PublicKey :
        /\ PUBLICKEYOF[ \E sk \in PrivateKey : pk = PUBLICKEYOF[sk] ] = pk
        /\ \E sk \in PrivateKey :
            LET prevBlk == ledgers[sender][lastHash] IN
            LET newBal == prevBlk.balance - amount IN
            LET newHash == CalculateHash(lastHash, << "Send", pk, amount, recipient >>) IN
            /\ newHash \in Hash
            /\ \A n \in Node :
                ledgers'[n] = [ledgers[n] EXCEPT ![newHash] = 
                    [type      |-> "Send",
                     account   |-> pk,
                     balance   |-> newBal,
                     prevHash  |-> lastHash,
                     srcPrev   |-> NoHash,
                     amount    |-> amount,
                     rep       |-> pk,
                     sig       |-> [sk2 \in PrivateKey |-> sk2 = sk]]]
            /\ lastHash' = newHash
            /\ \A n \in Node : receivedSets'[n] = receivedSets[n] \cup {newHash}
    /\ UNCHANGED << >>

CreateOpen(node, sendHash) ==
    /\ node \in Node
    /\ sendHash \in Hash
    /\ ledgers[node][sendHash].type = "Send"
    /\ ledgers[node][sendHash].account # NoBlockVal
    /\ let pk == PUBLICKEYOF[ \E sk \in PrivateKey : True ] in
       \E sk \in PrivateKey :
            LET srcBlk == ledgers[node][sendHash] IN
            LET newBal == srcBlk.amount IN
            LET newHash == CalculateHash(lastHash, << "Open", pk, newBal, sendHash >>) IN
            /\ newHash \in Hash
            /\ \A n \in Node :
                ledgers'[n] = [ledgers[n] EXCEPT ![newHash] =
                    [type      |-> "Open",
                     account   |-> pk,
                     balance   |-> newBal,
                     prevHash  |-> NoHash,
                     srcPrev   |-> sendHash,
                     amount    |-> 0,
                     rep       |-> pk,
                     sig       |-> [sk2 \in PrivateKey |-> sk2 = sk]]]
            /\ lastHash' = newHash
            /\ \A n \in Node : receivedSets'[n] = receivedSets[n] \cup {newHash}
    /\ UNCHANGED << >>

CreateReceive(receiverNode, sendHash) ==
    /\ receiverNode \in Node
    /\ sendHash \in Hash
    /\ ledgers[receiverNode][sendHash].type = "Send"
    /\ let pk == PUBLICKEYOF[ \E sk \in PrivateKey : True ] in
       \E sk \in PrivateKey :
            LET prevBlk == ledgers[receiverNode][lastHash] IN
            LET srcBlk == ledgers[receiverNode][sendHash] IN
            LET newBal == prevBlk.balance + srcBlk.amount IN
            LET newHash == CalculateHash(lastHash, << "Receive", pk, srcBlk.amount, sendHash >>) IN
            /\ newHash \in Hash
            /\ \A n \in Node :
                ledgers'[n] = [ledgers[n] EXCEPT ![newHash] =
                    [type      |-> "Receive",
                     account   |-> pk,
                     balance   |-> newBal,
                     prevHash  |-> lastHash,
                     srcPrev   |-> sendHash,
                     amount    |-> 0,
                     rep       |-> pk,
                     sig       |-> [sk2 \in PrivateKey |-> sk2 = sk]]]
            /\ lastHash' = newHash
            /\ \A n \in Node : receivedSets'[n] = receivedSets[n] \cup {newHash}
    /\ UNCHANGED << >>

CreateChangeRep(node, newRep) ==
    /\ node \in Node
    /\ newRep \in PublicKey
    /\ \E sk \in PrivateKey :
        LET prevBlk == ledgers[node][lastHash] IN
        LET newHash == CalculateHash(lastHash, << "ChangeRep", prevBlk.account, newRep >>) IN
        /\ newHash \in Hash
        /\ \A n \in Node :
            ledgers'[n] = [ledgers[n] EXCEPT ![newHash] =
                [type      |-> "ChangeRep",
                 account   |-> prevBlk.account,
                 balance   |-> prevBlk.balance,
                 prevHash  |-> lastHash,
                 srcPrev   |-> NoHash,
                 amount    |-> 0,
                 rep       |-> newRep,
                 sig       |-> [sk2 \in PrivateKey |-> sk2 = sk]]]
        /\ lastHash' = newHash
        /\ \A n \in Node : receivedSets'[n] = receivedSets[n] \cup {newHash}
    /\ UNCHANGED << >>

ProcessReceived(node) ==
    /\ node \in Node
    /\ \E h \in receivedSets[node] :
        LET blk == ledgers[node][h] IN
        /\ blk # NoBlock
        /\ \E sk \in PrivateKey :
            /\ PUBLICKEYOF[sk] = blk.account
            /\ blk.sig[sk] = TRUE
            /\ (blk.type = "Send" => 
                    LET senderBal == AccountBalance(ledgers[node], blk.prevHash) IN
                    blk.amount <= senderBal)
            /\ (blk.type = "Open" => 
                    /\ blk.srcPrev # NoHash
                    /\ ledgers[node][blk.srcPrev].type = "Send"
                    /\ ledgers[node][blk.srcPrev].account = blk.account)
            /\ (blk.type = "Receive" => 
                    /\ blk.srcPrev # NoHash
                    /\ ledgers[node][blk.srcPrev].type = "Send"
                    /\ blk.account = ledgers[node][blk.prevHash].account)
            /\ (blk.type = "ChangeRep" => TRUE)
            /\ \A n \in Node : ledgers'[n] = [ledgers[n] EXCEPT ![h] = blk]
            /\ receivedSets' = [receivedSets EXCEPT ![node] = receivedSets[node] \ {h}]
    /\ UNCHANGED lastHash

Next ==
    \/ CreateGenesis
    \/ \E sender, amount, recipient : CreateSend(sender, amount, recipient)
    \/ \E node, sh : CreateOpen(node, sh)
    \/ \E node, sh : CreateReceive(node, sh)
    \/ \E node, newRep : CreateChangeRep(node, newRep)
    \/ \E node : ProcessReceived(node)

(*-------------------------------------------------------------------*)
(* Specification *)

Spec == Init /\ [][Next]_<<lastHash, ledgers, receivedSets>>

(*-------------------------------------------------------------------*)
(* Type invariant *)

TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledgers \in [Node -> [Hash -> BlockRecord]]
    /\ receivedSets \in [Node -> SUBSET Hash]
    /\ \A n \in Node : \A h \in Hash : 
        (ledgers[n][h] = NoBlock) \/ 
        /\ ledgers[n][h].type \in BlockType
        /\ ledgers[n][h].account \in PublicKey
        /\ ledgers[n][h].balance \in Nat
        /\ ledgers[n][h].prevHash \in Hash
        /\ ledgers[n][h].srcPrev \in Hash
        /\ ledgers[n][h].amount \in Nat
        /\ ledgers[n][h].rep \in PublicKey
        /\ \A sk \in PrivateKey : ledgers[n][h].sig[sk] \in BOOLEAN

(*-------------------------------------------------------------------*)
(* Safety invariant: every block stored in every node's ledger has a valid signature *)

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET blk == ledgers[n][h] IN
            blk = NoBlock \/ 
                \E sk \in PrivateKey :
                    /\ PUBLICKEYOF[sk] = blk.account
                    /\ blk.sig[sk] = TRUE

====