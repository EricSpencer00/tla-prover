---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

\*-----------------------------------------------------------------
-- Constants (provided by the .cfg)
-----------------------------------------------------------------*/
CONSTANTS
    Hash,               \* Universe of possible block hashes
    NoHashVal,          \* Sentinel value meaning "no hash"
    PrivateKey,         \* Set of all private keys
    PublicKey,          \* Set of all public keys
    Node,               \* Set of network nodes
    GenesisBalance,    \* Total coin supply (a natural number)
    NoBlockVal,         \* Sentinel meaning "no block"
    CalculateHash,      \* Abstract hash operator
    NoHash,             \* Alias for NoHashVal
    NoBlock             \* Alias for NoBlockVal

\*-----------------------------------------------------------------
-- Derived sets
-----------------------------------------------------------------*/
HashSet == Hash \cup {NoHash}
BlockSet == { NoBlock } \cup { [type : {"Genesis","Send","Open","Receive","Change"},
                                hash : HashSet,
                                prevHash : HashSet,
                                account : PublicKey,
                                amount : Nat,
                                target : PublicKey,
                                rep    : PublicKey,
                                signature : PrivateKey] }

\*-----------------------------------------------------------------
-- State variables
-----------------------------------------------------------------*/
VARIABLES
    lastHash,                         \* The last created block hash (or NoHash)
    ledgers,                          \* [node \in Node -> [hash \in HashSet -> BlockSet]]
    received                         \* [node \in Node -> SUBSET HashSet]

\*-----------------------------------------------------------------
-- Helper definitions
-----------------------------------------------------------------*/

\* Mapping from private keys to their public counterpart (bijective)
KeyMap == [pk \in PrivateKey |-> CHOOSE pub \in PublicKey : pk \in PrivateKey \land pub \in PublicKey]

\* Empty ledger: every hash maps to the sentinel NoBlock
EmptyLedger == [h \in HashSet |-> NoBlock]

\* Initial state
Init ==
    /\ lastHash = NoHash
    /\ ledgers = [n \in Node |-> EmptyLedger]
    /\ received = [n \in Node |-> {}]

\*-----------------------------------------------------------------
-- Block constructors (return a block record)
-----------------------------------------------------------------*/

GenesisBlock(pk) ==
    [type      |-> "Genesis",
     hash      |-> CalculateHash([type |-> "Genesis", pk |-> keyMap[pk]]),
     prevHash  |-> NoHash,
     account   |-> KeyMap[pk],
     amount    |-> GenesisBalance,
     target    |-> NoPublic,
     rep       |-> NoPublic,
     signature |-> pk]

SendBlock(pk, prev, amt, tgt) ==
    [type      |-> "Send",
     hash      |-> CalculateHash([type |-> "Send", pk |-> pk, prev |-> prev, amt |-> amt, tgt |-> tgt]),
     prevHash  |-> prev,
     account   |-> KeyMap[pk],
     amount    |-> amt,
     target    |-> tgt,
     rep       |-> NoPublic,
     signature |-> pk]

OpenBlock(pk, sendHash) ==
    [type      |-> "Open",
     hash      |-> CalculateHash([type |-> "Open", pk |-> pk, send |-> sendHash]),
     prevHash  |-> NoHash,
     account   |-> KeyMap[pk],
     amount    |-> 0,
     target    |-> NoPublic,
     rep       |-> NoPublic,
     signature |-> pk]

ReceiveBlock(pk, prev, sendHash) ==
    [type      |-> "Receive",
     hash      |-> CalculateHash([type |-> "Receive", pk |-> pk, prev |-> prev, send |-> sendHash]),
     prevHash  |-> prev,
     account   |-> KeyMap[pk],
     amount    |-> 0,
     target    |-> NoPublic,
     rep       |-> NoPublic,
     signature |-> pk]

ChangeRepBlock(pk, prev, newRep) ==
    [type      |-> "Change",
     hash      |-> CalculateHash([type |-> "Change", pk |-> pk, prev |-> prev, rep |-> newRep]),
     prevHash  |-> prev,
     account   |-> KeyMap[pk],
     amount    |-> 0,
     target    |-> NoPublic,
     rep       |-> newRep,
     signature |-> pk]

\*-----------------------------------------------------------------
-- Balance calculation (walk the account chain)
-----------------------------------------------------------------*/

Balance(ledger, acct) ==
    LET
        chain == { h \in HashSet :
                    ledger[h] # NoBlock /\ ledger[h].account = acct }
        recv  == { h \in chain :
                    ledger[h].type = "Receive" }
        send  == { h \in chain :
                    ledger[h].type = "Send" }
    IN
        ( IF "Genesis" \in { ledger[h].type : h \in chain } THEN GenesisBalance ELSE 0 )
        +  Sum( { ledger[h].amount : h \in recv } )
        -  Sum( { ledger[h].amount : h \in send } )

\*-----------------------------------------------------------------
-- Signature validation (abstract, always true for correct key)
-----------------------------------------------------------------*/

ValidSignature(b) ==
    /\ b.signature \in PrivateKey
    /\ KeyMap[b.signature] = b.account

\*-----------------------------------------------------------------
-- Actions
-----------------------------------------------------------------*/

CreateGenesis ==
    \E pk \in PrivateKey :
        /\ lastHash = NoHash
        /\ \A n \in Node :
            LET bg == GenesisBlock(pk) IN
                /\ ledgers' = [ ledgers EXCEPT ![n][bg.hash] = bg ]
                /\ received' = [ received EXCEPT ![n] = {} ]
        /\ lastHash' = GenesisBlock(pk).hash
        /\ UNCHANGED << >>

CreateSend ==
    \E n \in Node, pk \in PrivateKey, prev, tgt \in HashSet, amt \in Nat :
        /\ lastHash # NoHash
        /\ let bPrev == ledgers[n][prev] in
            /\ bPrev # NoBlock
            /\ bPrev.account = KeyMap[pk]               \* sender owns prev block
            /\ bPrev.type # "Send"                       \* cannot send from a Send block
            /\ Balance(ledgers[n], bPrev.account) >= amt
        /\ let b == SendBlock(pk, prev, amt, tgt) in
        /\ lastHash' = b.hash
        /\ ledgers' = [ ledgers EXCEPT
            ![n][b.hash] = b ]
        /\ received' = [ received EXCEPT
            ![m \in Node] = @ \cup { b.hash } ]      \* broadcast to all nodes
        /\ UNCHANGED << >>

CreateOpen ==
    \E n \in Node, pk \in PrivateKey, sendHash \in HashSet :
        /\ let snd == ledgers[n][sendHash] in
            /\ snd # NoBlock
            /\ snd.type = "Send"
            /\ snd.target = KeyMap[pk]
            /\ ~\E h \in HashSet : ledgers[n][h].type = "Open" /\ ledgers[n][h].account = KeyMap[pk]
        /\ let b == OpenBlock(pk, sendHash) in
        /\ lastHash' = b.hash
        /\ ledgers' = [ ledgers EXCEPT
            ![n][b.hash] = b ]
        /\ received' = [ received EXCEPT
            ![m \in Node] = @ \cup { b.hash } ]
        /\ UNCHANGED << >>

CreateReceive ==
    \E n \in Node, pk \in PrivateKey, prev, sendHash \in HashSet :
        /\ let snd == ledgers[n][sendHash] in
            /\ snd # NoBlock /\ snd.type = "Send" /\ snd.target = KeyMap[pk]
        /\ let prevBlk == ledgers[n][prev] in
            /\ prevBlk # NoBlock /\ prevBlk.account = KeyMap[pk]
        /\ ~\E h \in HashSet :
                ledgers[n][h].type = "Receive" /\ ledgers[n][h].prevHash = prev /\ ledgers[n][h].target = sendHash
        /\ let b == ReceiveBlock(pk, prev, sendHash) in
        /\ lastHash' = b.hash
        /\ ledgers' = [ ledgers EXCEPT
            ![n][b.hash] = b ]
        /\ received' = [ received EXCEPT
            ![m \in Node] = @ \cup { b.hash } ]
        /\ UNCHANGED << >>

CreateChange ==
    \E n \in Node, pk \in PrivateKey, prev, newRep \in PublicKey :
        /\ let prevBlk == ledgers[n][prev] in
            /\ prevBlk # NoBlock /\ prevBlk.account = KeyMap[pk]
        /\ let b == ChangeRepBlock(pk, prev, newRep) in
        /\ lastHash' = b.hash
        /\ ledgers' = [ ledgers EXCEPT
            ![n][b.hash] = b ]
        /\ received' = [ received EXCEPT
            ![m \in Node] = @ \cup { b.hash } ]
        /\ UNCHANGED << >>

ProcessBlock ==
    \E n \in Node, h \in received[n] :
        /\ ledgers[n][h] = NoBlock
        /\ LET b == ( * the block data is derived from the hash using a reverse map;
                     * for this abstract model we just assume the block exists as a constant *)
            b == CHOOSE blk \in BlockSet : blk.hash = h
        IN
        /\ ValidSignature(b)
        /\ ( IF b.prevHash # NoHash THEN ledgers[n][b.prevHash] # NoBlock ELSE TRUE )
        /\ ( IF b.type = "Send" THEN
                Balance(ledgers[n], b.account) >= b.amount
             ELSE TRUE )
        /\ ledgers' = [ ledgers EXCEPT ![n][h] = b ]
        /\ received' = [ received EXCEPT ![n] = @ \ { h } ]
        /\ UNCHANGED lastHash

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock
    \/ UNCHANGED << lastHash, ledgers, received >>

Spec == Init /\ [][Next]_<<lastHash, ledgers, received>>

\*-----------------------------------------------------------------
-- Type Invariant (basic type safety)
-----------------------------------------------------------------*/
TypeOK ==
    /\ lastHash \in HashSet
    /\ ledgers \in [Node -> [HashSet -> BlockSet]]
    /\ received \in [Node -> SUBSET HashSet]

\*-----------------------------------------------------------------
-- Safety invariant (cryptographic correctness)
-----------------------------------------------------------------*/
SafetyInvariant ==
    \A n \in Node :
        \A h \in HashSet :
            LET b == ledgers[n][h] IN
                IF b = NoBlock THEN TRUE
                ELSE ValidSignature(b)

\*-----------------------------------------------------------------
-- The invariants required by the .cfg
-----------------------------------------------------------------*/
Inv == TypeOK /\ SafetyInvariant

\*-----------------------------------------------------------------
-- THEOREM: Spec => Inv
-----------------------------------------------------------------*/
THEOREM Spec => Inv

=============================================================================