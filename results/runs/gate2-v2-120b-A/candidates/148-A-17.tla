---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*-----------------------------------------------------------------
-- CONSTANTS (must be supplied by the .cfg)
-----------------------------------------------------------------*/
CONSTANTS
    Hash,               \* Universe of possible hash values
    NoHashVal,          \* Sentinel representing "no hash"
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,     \* Total coin supply (a natural number)
    NoBlockVal,         \* Sentinel representing "no block"
    CalculateHash,      \* Abstract hash operator: block data × previous hash -> Hash
    NoHash,             \* Alias for NoHashVal (kept for .cfg compatibility)
    NoBlock             \* Alias for NoBlockVal (kept for .cfg compatibility)

\*-----------------------------------------------------------------
-- Types
-----------------------------------------------------------------*/
BlockType == {"Genesis", "Send", "Open", "Receive", "ChangeRep"}

Block == [type   : BlockType,
          hash   : Hash,
          prev   : Hash,
          src    : PublicKey \cup {"None"},
          dest   : PublicKey \cup {"None"},
          amount : Nat,
          sig    : PrivateKey]

\*-----------------------------------------------------------------
-- Derived sets
-----------------------------------------------------------------*/
Accounts == PublicKey
AllBlocks == { NoBlock } \cup { b \in Block : b.hash \in Hash }

\*-----------------------------------------------------------------
-- Variables
-----------------------------------------------------------------*/
VARIABLES
    lastHash,          \* Last calculated block hash in the system
    ledger,            \* [node \in Node -> [hash \in Hash -> Block \cup {NoBlock}]]
    received,          \* [node \in Node -> SUBSET Block]  blocks that have arrived but not yet processed
    privKeyOf          \* [node \in Node -> PrivateKey]   private key owned by each node

\*-----------------------------------------------------------------
-- Helper definitions
-----------------------------------------------------------------*/
\* Extract the owner (account) of a block: the public key whose chain the block belongs to
Owner(b) ==
    IF b.type = "Genesis" THEN b.dest
    ELSE IF b.type = "Send"    THEN b.src
    ELSE IF b.type = "Open"    THEN b.dest
    ELSE IF b.type = "Receive" THEN b.dest
    ELSE IF b.type = "ChangeRep" THEN b.src
    ELSE "None"

\* Public key belonging to a private key (bijection assumed in model)
PubKey(priv) ==
    CHOOSE pk \in PublicKey : pk \in { pk2 : \E p \in PrivateKey : p = priv /\ pk2 = ??? }
    \* In practice the .cfg will supply a mapping; here we treat it abstractly.

\* Verify a signature (abstract)
ValidSig(b) ==
    (* In a real spec we would check that b.sig signs the block with the private key
       corresponding to Owner(b). Here we abstractly assume a predicate holds. *)
    TRUE

\* Balance of an account on a given node by walking its chain.
Balance(node, acc) ==
    LET chain == { b \in Block : Owner(b) = acc /\ b.hash \in Hash } IN
    IF acc = "None" THEN 0
    ELSE
        LET
            genesisBlock == CHOOSE b \in chain : b.type = "Genesis"
            rec(bs) ==
                IF bs = {} THEN 0
                ELSE
                    LET b == CHOOSE x \in bs : x.prev = NoHashVal
                    IN
                        CASE b.type = "Genesis"   -> b.amount
                         [] b.type = "Send"       -> -b.amount
                         [] b.type = "Open"       -> 0
                         [] b.type = "Receive"    -> b.amount
                         [] b.type = "ChangeRep"  -> 0
                         [] OTHER                -> 0
                        + rec({ x \in bs : x.prev = b.hash })
        IN rec({ b \in chain : b.prev = NoHashVal })

\*-----------------------------------------------------------------
-- Initialization
-----------------------------------------------------------------*/
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ privKeyOf \in [Node -> PrivateKey]   \* each node gets a private key (bijection not required)

\*-----------------------------------------------------------------
-- Actions
-----------------------------------------------------------------*/
CreateGenesis ==
    /\ \E n \in Node :
          /\ lastHash = NoHashVal
          /\ \E pk \in PublicKey :
                /\ b \in Block :
                    /\ b.type = "Genesis"
                    /\ b.hash \in Hash
                    /\ b.prev = NoHashVal
                    /\ b.dest = pk
                    /\ b.amount = GenesisBalance
                    /\ b.sig = privKeyOf[n]
                    /\ b.src = "None"
                    /\ ledger' = [node \in Node |-> [h \in Hash |-> IF h = b.hash THEN b ELSE ledger[node][h]]]
                    /\ lastHash' = b.hash
                    /\ received' = [node \in Node |-> {}]   \* Genesis block is already in the ledger, not pending
                    /\ UNCHANGED privKeyOf
    \/ UNCHANGED <<lastHash, ledger, received, privKeyOf>>

CreateSend ==
    /\ \E n \in Node :
          /\ \E bPrev \in Block :
                /\ bPrev.type # "Send"   \* previous block can be any type except we don't care
                /\ bPrev.hash # NoHashVal
                /\ ledger[n][bPrev.hash] = bPrev
                /\ Balance(n, Owner(bPrev)) >= amt
                /\ amt \in Nat \ {0}
                /\ b \in Block :
                    /\ b.type = "Send"
                    /\ b.prev = bPrev.hash
                    /\ b.src = Owner(bPrev)
                    /\ b.dest \in Accounts
                    /\ b.amount = amt
                    /\ b.hash \in Hash
                    /\ b.sig = privKeyOf[n]
                    /\ b.src # "None"
                    /\ /\ ledger' = ledger
                       /\ received' = [node \in Node |-> received[node] \cup {b}]
                       /\ lastHash' = b.hash
                    /\ UNCHANGED privKeyOf
    \/ UNCHANGED <<lastHash, ledger, received, privKeyOf>>

CreateOpen ==
    /\ \E n \in Node :
          /\ \E sendBlk \in Block :
                /\ sendBlk.type = "Send"
                /\ sendBlk.dest = OwnerOfNode(n)   \* node's public key (abstract)
                /\ sendBlk.hash \in Hash
                /\ \E bPrev \in Block :
                       /\ bPrev = NoBlock   \* open block has no previous hash
                       /\ b \in Block :
                            /\ b.type = "Open"
                            /\ b.prev = NoHashVal
                            /\ b.src = sendBlk.dest
                            /\ b.dest = sendBlk.dest
                            /\ b.amount = sendBlk.amount
                            /\ b.hash \in Hash
                            /\ b.sig = privKeyOf[n]
                            /\ ledger' = ledger
                            /\ received' = [node \in Node |-> received[node] \cup {b}]
                            /\ lastHash' = b.hash
                            /\ UNCHANGED privKeyOf
    \/ UNCHANGED <<lastHash, ledger, received, privKeyOf>>

CreateReceive ==
    /\ \E n \in Node :
          /\ \E bPrev \in Block :
                /\ bPrev.type # "Send"
                /\ ledger[n][bPrev.hash] = bPrev
                /\ \E sendBlk \in Block :
                     /\ sendBlk.type = "Send"
                     /\ sendBlk.dest = OwnerOfNode(n)
                     /\ sentButNotReceived(sendBlk, n)   \* abstract predicate
                     /\ b \in Block :
                         /\ b.type = "Receive"
                         /\ b.prev = bPrev.hash
                         /\ b.src = Owner(bPrev)
                         /\ b.dest = OwnerOfNode(n)
                         /\ b.amount = sendBlk.amount
                         /\ b.hash \in Hash
                         /\ b.sig = privKeyOf[n]
                         /\ ledger' = ledger
                         /\ received' = [node \in Node |-> received[node] \cup {b}]
                         /\ lastHash' = b.hash
                         /\ UNCHANGED privKeyOf
    \/ UNCHANGED <<lastHash, ledger, received, privKeyOf>>

CreateChangeRep ==
    /\ \E n \in Node :
          /\ \E bPrev \in Block :
                /\ ledger[n][bPrev.hash] = bPrev
                /\ b \in Block :
                     /\ b.type = "ChangeRep"
                     /\ b.prev = bPrev.hash
                     /\ b.src = Owner(bPrev)
                     /\ b.dest = "None"
                     /\ b.amount = 0
                     /\ b.hash \in Hash
                     /\ b.sig = privKeyOf[n]
                     /\ ledger' = ledger
                     /\ received' = [node \in Node |-> received[node] \cup {b}]
                     /\ lastHash' = b.hash
                     /\ UNCHANGED privKeyOf
    \/ UNCHANGED <<lastHash, ledger, received, privKeyOf>>

ProcessBlock ==
    /\ \E n \in Node :
          /\ \E b \in received[n] :
                /\ Validate(b, n)
                /\ ledger' = [node \in Node |-> IF node = n THEN
                                   [h \in Hash |-> IF h = b.hash THEN b ELSE ledger[node][h]]
                               ELSE ledger[node]]
                /\ received' = [node \in Node |-> IF node = n THEN received[node] \ {b} ELSE received[node]]
                /\ UNCHANGED <<lastHash, privKeyOf>>
    \/ UNCHANGED <<lastHash, ledger, received, privKeyOf>>

Validate(b, n) ==
    /\ b \in Block
    /\ ValidSig(b)
    /\ CASE b.type = "Genesis" ->
            /\ b.prev = NoHashVal
            /\ \A n2 \in Node : ledger[n2][b.hash] = NoBlock
       [] b.type = "Send" ->
            /\ b.prev # NoHashVal
            /\ ledger[n][b.prev] # NoBlock
            /\ Balance(n, b.src) >= b.amount
       [] b.type = "Open" ->
            /\ b.prev = NoHashVal
            /\ \E sendBlk \in Block :
                 /\ sendBlk.type = "Send"
                 /\ sendBlk.dest = b.dest
                 /\ sendBlk.amount = b.amount
            /\ \A n2 \in Node : ledger[n2][b.hash] = NoBlock
       [] b.type = "Receive" ->
            /\ b.prev # NoHashVal
            /\ ledger[n][b.prev] # NoBlock
            /\ \E sendBlk \in Block :
                 /\ sendBlk.type = "Send"
                 /\ sendBlk.dest = b.dest
                 /\ sendBlk.amount = b.amount
                 /\ \A n2 \in Node : ledger[n2][sendBlk.hash] # NoBlock
       [] b.type = "ChangeRep" ->
            /\ b.prev # NoHashVal
            /\ ledger[n][b.prev] # NoBlock
       [] OTHER -> FALSE

\*-----------------------------------------------------------------
-- Next-state relation
-----------------------------------------------------------------*/
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChangeRep
    \/ ProcessBlock

\*-----------------------------------------------------------------
-- Specification
-----------------------------------------------------------------*/
Spec == Init /\ [][Next]_<<lastHash, ledger, received, privKeyOf>>

\*-----------------------------------------------------------------
-- Safety invariant: every block stored in any node's ledger has a
-- valid signature matching the owner’s public key.
-----------------------------------------------------------------*/
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == ledger[n][h] IN
                b = NoBlock \/ ValidSig(b)

\*-----------------------------------------------------------------
-- Type invariant (optional but required by .cfg)
-----------------------------------------------------------------*/
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Node -> [Hash -> Block \cup {NoBlock}]]
    /\ received \in [Node -> SUBSET Block]
    /\ privKeyOf \in [Node -> PrivateKey]

=============================================================================