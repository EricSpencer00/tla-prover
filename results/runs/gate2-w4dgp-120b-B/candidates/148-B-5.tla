---- MODULE Nano ----
EXTENDS Naturals, Bags

Constantss
    Hash, CalculateHash(_,_,_,_), PrivateKey, PublicKey, KeyPair, Node
    GenesisBalance, Ownership

VARIABLES lastHash, distributedLedger, received

(***************************************************************************)
(* An action calculating the hash of a block, using the network's hash      *)
(* function wrapped with the network's namespace, so it cannot clash with     *)
(* any other hash function in scope.                                        *)
(* NOTE: In the original spec the hash function was just a free variable,   *)
(* which means the type-correctness of a block's hash depends on whatever    *)
(* other module happens to have a function called "CalculateHash" in scope.  *)
(* This is exactly why we wrap it in a namespace when we import it.          *)
(* CURRENTLY the function takes a source block and a target block, plus the *)
(* hash of the source block, and returns the target block's hash.            *)
(***************************************************************************)

ASSUME CalculateHash \in [Block -> Hash -> Hash -> Hash]

VARIABLES lastHash, distributedLedger, received
ASSUME /\ lastHash \in {NoHash} \union Hash
       /\ distributedLedger \in [Node -> [Hash -> SignedBlock \union {NoBlock}]]
       /\ received \subseteq [Node -> SUBSET SignedBlock]

Hash = { h1, h2, h3 }
NoHash = NoHash
NoBlock = NoBlock

\* The set of all blocks that can be recorded on the blockchain, with a
\* genesis block, a send block, an open block, a receive block, and a
\* change-rep block.
Block ==
    [type : { "genesis", "send", "receive", "open", "change" }]
    \union [previous : Hash, balance : 0..1, destination : PublicKey]
    \union [account : PublicKey, source : Hash]
    \union [account : PublicKey, source : Hash, rep : PublicKey]
    \union [previous : Hash, rep : PublicKey]
    \union [previous : Hash, source : Hash]

Signature ==
    [data : Hash, signedBy : PrivateKey]

(***************************************************************************)
(* Return the public key of the block's source account, whatever the block  *)
(* type is.                                                                  *)
(***************************************************************************)

PublicKeyOf(ledger, hash) ==
    LET signedBlock == ledger[hash]
        block == signedBlock.block
    IN IF block.type \in { "genesis", "open" }
       THEN block.account
       ELSE IF block.type = "send"
            THEN block.destination
            ELSE PublicKeyOf(ledger, block.previous)

\* Validate the block's signature against the account that owns the block.
ValidateSignature(signedBlock, ledger) ==
    LET block == signedBlock.block
    IN block.type \in { "genesis", "send" }
       => (PublicKeyOf(ledger, block.previous) = block.account)
       /\ block \in ledger[PublicKeyOf(ledger, block.previous)]

\* The real action is: the genesis block is created once on every node's
\* ledger at the same hash, and is signed by the node that owns it.
CreateGenesisBlock ==
    /\ \A node \in Node : ~\E hash \in Hash : distributedLedger[node][hash] # NoBlock
    /\ \E block \in Block :
        /\ block.type = "genesis"
        /\ \E hash \in Hash :
            \A node \in Node :
                distributedLedger' = [distributedLedger EXCEPT ![node][hash] = block]
    /\ UNCHANGED received

\* A node creates a block from the ledger it owns, records the block on its
\* own ledger, and pushes the block into its outgoing network queue.
CreateBlock(node, block) ==
    /\ \E hash \in Hash :
        /\ block.type \notin { "genesis", "send" }
        /\ ~\E h \in Hash : distributedLedger[node][h] = block
        /\ distributedLedger' = [distributedLedger EXCEPT ![node][hash] = block]
        /\ received' = [received EXCEPT ![node] = @ \union { block }]
    /\ UNCHANGED lastHash

(***************************************************************************)
(* The only real safety property: no two distinct blocks can ever have the  *)
(* same hash, because the network's hash function is collision-resistant.  *)
(***************************************************************************)

NoHashCollision ==
    \A node \in Node : \A hash \in Hash :
        \A other : other # hash => distributedLedger[node][hash] # distributedLedger[node][other]

====