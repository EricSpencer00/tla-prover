---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* -------------------------------------------------
\* Constants (as required by the .cfg)
\* -------------------------------------------------
CONSTANTS
    Hash,            \* Set of possible block hashes
    NoHashVal,       \* Sentinel value meaning “no hash”
    PrivateKey,      \* Set of private keys
    PublicKey,       \* Set of public keys
    Node,            \* Set of network nodes
    GenesisBalance,  \* Total supply of coins (a natural number)
    NoBlockVal,      \* Sentinel value meaning “no block”
    CalculateHash,   \* Abstract hash calculation operator
    NoHash,          \* Alias for NoHashVal (for readability)
    NoBlock          \* Alias for NoBlockVal (for readability)

\* -------------------------------------------------
\* Types derived from the description
\* -------------------------------------------------
BlockType == {"Genesis", "Send", "Open", "Receive", "ChangeRep"}

Block == [
    type          : BlockType,
    hash          : Hash,
    prev          : Hash,          \* previous block in the same account chain
    sender        : PublicKey,     \* who creates the block (or NoPublic for genesis)
    recipient     : PublicKey,     \* destination (or NoPublic if not applicable)
    amount        : Nat,           \* amount transferred (0 if not applicable)
    representative: PublicKey,    \* voting rep (or NoPublic if not applicable)
    signature     : PublicKey      \* public key that signed the block (identifies owner)
]

\* -------------------------------------------------
\* Variables
\* -------------------------------------------------
VARIABLES
    lastHash,          \* Last calculated block hash (or NoHashVal)
    ledger,            \* [node \in Node |-> [h \in Hash |-> NoBlock]]
    received,          \* [node \in Node |-> SUBSET Hash]
    privToPub          \* mapping from PrivateKey to PublicKey (fixed)

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
\* The set of all accounts is the set of public keys
Accounts == PublicKey

\* Returns the block stored under hash h in node n's ledger, or NoBlock if none
BlockAt(node, h) == ledger[node][h]

\* The set of blocks actually present (not NoBlock) in node n's ledger
BlocksInLedger(node) == { h \in Hash : BlockAt(node, h) # NoBlock }

\* Find the hash of the last block in the chain of account acc on node n
LastBlockInChain(node, acc) ==
    LET Chain == { h \in Hash :
        BlockAt(node, h).type # "Genesis" /\ BlockAt(node, h).sender = acc }
    IN IF Chain = {} THEN NoHash
       ELSE CHOOSE h \in Chain : 
            \A h2 \in Chain : BlockAt(node, h2).prev # h => FALSE
            (* above picks the block whose prev is not another block in the chain *)

\* Balance of account acc on node n, computed by walking its chain
Balance(node, acc) ==
    LET Rec(accHash) ==
        IF accHash = NoHash THEN 0
        ELSE
            LET blk == BlockAt(node, accHash) IN
            CASE blk.type = "Genesis" -> blk.amount
               [] blk.type = "Send"    -> Rec(blk.prev) - blk.amount
               [] blk.type = "Receive" -> Rec(blk.prev) + blk.amount
               [] blk.type = "Open"    -> blk.amount
               [] blk.type = "ChangeRep" -> Rec(blk.prev)
            [] OTHER -> 0
    IN Rec(LastBlockInChain(node, acc))

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ privToPub \in [pk \in PrivateKey |-> PublicKey]
    /\ \A pk \in PrivateKey : privToPub[pk] \in PublicKey
    /\ \A pk \in PrivateKey : privToPub[pk] # NoPublic

\* -------------------------------------------------
\* Block creation actions
\* -------------------------------------------------
CreateGenesis ==
    /\ \E pk \in PrivateKey :
        LET pub == privToPub[pk] IN
        LET blk == [
            type           |-> "Genesis",
            hash           |-> CalculateHash([type |-> "Genesis", sender |-> pub,
                                            amount |-> GenesisBalance,
                                            prev |-> NoHashVal,
                                            recipient |-> NoPublic,
                                            representative |-> pub]),
            prev           |-> NoHashVal,
            sender         |-> pub,
            recipient      |-> NoPublic,
            amount         |-> GenesisBalance,
            representative |-> pub,
            signature      |-> pub
        ] IN
        /\ lastHash = NoHashVal
        /\ lastHash' = blk.hash
        /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![blk.hash] = blk]
        /\ received' = received
        /\ privToPub' = privToPub
    /\ UNCHANGED <<>>

CreateSend ==
    /\ \E node \in Node :
        /\ \E pk \in PrivateKey :
            LET senderPub == privToPub[pk] IN
            LET prevHash == LastBlockInChain(node, senderPub) IN
            LET senderBal == Balance(node, senderPub) IN
            /\ senderBal > 0
            /\ \E amount \in Nat :
                /\ amount > 0 /\ amount <= senderBal
                /\ \E recPub \in PublicKey :
                    LET blk == [
                        type           |-> "Send",
                        hash           |-> CalculateHash([type |-> "Send",
                                                            sender |-> senderPub,
                                                            recipient |-> recPub,
                                                            amount |-> amount,
                                                            prev |-> prevHash]),
                        prev           |-> prevHash,
                        sender         |-> senderPub,
                        recipient      |-> recPub,
                        amount         |-> amount,
                        representative |-> NoPublic,
                        signature      |-> senderPub
                    ] IN
                    /\ lastHash' = blk.hash
                    /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![blk.hash] = blk]
                    /\ received' = [n \in Node |-> received[n] \cup {blk.hash}]
                    /\ UNCHANGED privToPub
    /\ UNCHANGED <<>>

CreateOpen ==
    /\ \E node \in Node :
        /\ \E pk \in PrivateKey :
            LET ownerPub == privToPub[pk] IN
            /\ ownerPub # NoPublic
            /\ \E sendHash \in Hash :
                /\ sendHash \in BlocksInLedger(node)
                /\ LET sb == BlockAt(node, sendHash) IN
                   sb.type = "Send" /\ sb.recipient = ownerPub
                /\ \E openBlk == [
                        type           |-> "Open",
                        hash           |-> CalculateHash([type |-> "Open",
                                                            sender |-> sb.sender,
                                                            recipient |-> ownerPub,
                                                            amount |-> sb.amount,
                                                            prev |-> NoHashVal]),
                        prev           |-> NoHashVal,
                        sender         |-> sb.sender,
                        recipient      |-> ownerPub,
                        amount         |-> sb.amount,
                        representative |-> sb.sender,
                        signature      |-> ownerPub
                    ] :
                    /\ lastHash' = openBlk.hash
                    /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![openBlk.hash] = openBlk]
                    /\ received' = [n \in Node |-> received[n] \cup {openBlk.hash}]
                    /\ UNCHANGED privToPub
    /\ UNCHANGED <<>>

CreateReceive ==
    /\ \E node \in Node :
        /\ \E pk \in PrivateKey :
            LET ownerPub == privToPub[pk] IN
            LET prevHash == LastBlockInChain(node, ownerPub) IN
            /\ prevHash # NoHashVal
            /\ \E sendHash \in Hash :
                /\ sendHash \in BlocksInLedger(node)
                /\ LET sb == BlockAt(node, sendHash) IN
                   sb.type = "Send" /\ sb.recipient = ownerPub
                /\ \E recvBlk == [
                        type           |-> "Receive",
                        hash           |-> CalculateHash([type |-> "Receive",
                                                            sender |-> sb.sender,
                                                            recipient |-> ownerPub,
                                                            amount |-> sb.amount,
                                                            prev |-> prevHash,
                                                            source |-> sendHash]),
                        prev           |-> prevHash,
                        sender         |-> sb.sender,
                        recipient      |-> ownerPub,
                        amount         |-> sb.amount,
                        representative |-> NoPublic,
                        signature      |-> ownerPub
                    ] :
                    /\ lastHash' = recvBlk.hash
                    /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![recvBlk.hash] = recvBlk]
                    /\ received' = [n \in Node |-> received[n] \cup {recvBlk.hash}]
                    /\ UNCHANGED privToPub
    /\ UNCHANGED <<>>

CreateChangeRep ==
    /\ \E node \in Node :
        /\ \E pk \in PrivateKey :
            LET ownerPub == privToPub[pk] IN
            LET prevHash == LastBlockInChain(node, ownerPub) IN
            /\ prevHash # NoHashVal
            /\ \E newRep \in PublicKey :
                LET blk == [
                    type           |-> "ChangeRep",
                    hash           |-> CalculateHash([type |-> "ChangeRep",
                                                        sender |-> ownerPub,
                                                        representative |-> newRep,
                                                        prev |-> prevHash]),
                    prev           |-> prevHash,
                    sender         |-> ownerPub,
                    recipient      |-> NoPublic,
                    amount         |-> 0,
                    representative |-> newRep,
                    signature      |-> ownerPub
                ] IN
                /\ lastHash' = blk.hash
                /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![blk.hash] = blk]
                /\ received' = [n \in Node |-> received[n] \cup {blk.hash}]
                /\ UNCHANGED privToPub
    /\ UNCHANGED <<>>

\* -------------------------------------------------
\* Processing (validation) of received blocks
\* -------------------------------------------------
ProcessReceived ==
    /\ \E node \in Node :
        /\ \E h \in received[node] :
            LET blk == BlockAt(node, h) IN
            /\ blk # NoBlock
            /\ /\* Signature must match the block's owner (sender) *\
               blk.signature = blk.sender
            /\ /\* If the block references a previous hash, that hash must already exist *\
               (blk.prev = NoHashVal \/ BlockAt(node, blk.prev) # NoBlock)
            /\ /\* Type‑specific validation *\
               IF blk.type = "Send" THEN
                   Balance(node, blk.sender) >= blk.amount
               ELSE IF blk.type = "Open" THEN
                   blk.prev = NoHashVal /\ blk.amount > 0
               ELSE IF blk.type = "Receive" THEN
                   blk.prev # NoHashVal /\ blk.amount = BlockAt(node, blk.source).amount
               ELSE IF blk.type = "ChangeRep" THEN
                   blk.prev # NoHashVal
               ELSE IF blk.type = "Genesis" THEN
                   True
               ELSE
                   FALSE
            /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![h] = blk]
            /\ received' = [n \in Node |-> received[n] \ {h}]
            /\ UNCHANGED << lastHash, privToPub >>
    /\ UNCHANGED <<>>

\* -------------------------------------------------
\* Next-state relation
\* -------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChangeRep
    \/ ProcessReceived

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received, privToPub>>

\* -------------------------------------------------
\* Safety invariant (cryptographic invariant)
\* -------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET blk == ledger[n][h] IN
            blk = NoBlock => TRUE
            : blk.signature = blk.sender

\* -------------------------------------------------
\* Type invariant (ensuring variables stay in declared domains)
\* -------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]
    /\ privToPub \in [PrivateKey -> PublicKey]

\* -------------------------------------------------
\* Theorems (optional, for TLC)
\* -------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafetyInvariant

====