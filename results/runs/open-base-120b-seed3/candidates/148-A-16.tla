---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  CONSTANTS (to be supplied in the .cfg file)                           *)
(***************************************************************************)
CONSTANTS
    Hash,            \* Set of all possible block hashes
    NoHash,          \* Sentinel hash value meaning "no previous hash"
    NoHashVal,       \* Alias for NoHash (may be used by the cfg)
    PrivateKey,      \* Set of private keys
    PublicKey,       \* Set of public keys
    Node,            \* Set of network nodes
    GenesisBalance,  \* Natural number – total supply at genesis
    NoBlock,         \* Sentinel block value meaning "empty slot"
    NoBlockVal,      \* Alias for NoBlock (may be used by the cfg)
    CalculateHash,   \* Abstract hash‑calculation operator (will be overridden)
    \* Additional constants that help tie keys to nodes
    Owner,           \* [Node -> PrivateKey]  mapping each node to its private key
    PubKeyOfPriv,    \* [PrivateKey -> PublicKey]  mapping a private key to its public key
    AccountOfPub    \* [PublicKey -> Node]  (optional, may be left uninterpreted)

(***************************************************************************)
(*  STATE VARIABLES                                                       *)
(***************************************************************************)
VARIABLES
    LastHash,        \* The hash of the most recently created block
    Ledger,          \* [Node -> [Hash -> Block]]  each node's local copy of the ledger
    Received         \* [Node -> SUBSET Block]  blocks that have arrived but not yet validated

(***************************************************************************)
(*  BASIC TYPES                                                            *)
(***************************************************************************)

Block ==
    [ type        : {"genesis", "send", "open", "receive", "change"},
      account     : PublicKey,           \* owner of the account chain
      prevHash    : Hash,                \* hash of the previous block in the chain
      amount      : Nat,                 \* amount transferred (0 for types that don't use it)
      recipient   : PublicKey,           \* destination account (only for send/open)
      representative : PublicKey,       \* voting representative (only for change)
      signature   : STRING               \* abstract signature value
    ]

(***************************************************************************)
(*  ABSTRACT CRYPTOGRAPHIC OPERATORS                                      *)
(***************************************************************************)

(* Sign(priv, data) returns an abstract signature string *)
Sign(priv, data) == (* uninterpreted *) ""

(* Verify(pub, data, sig) returns TRUE iff the signature matches *)
Verify(pub, data, sig) == (* uninterpreted *) TRUE

(* The hash calculation operator that the .cfg file will replace with a
   concrete finite implementation.  Here we give a simple uninterpreted
   definition that merely asserts the result is a member of Hash. *)
CalculateHashImpl(block, prev) ==
    CHOOSE h \in Hash : TRUE

/***************************************************************************)
(*  INITIAL STATE                                                          *)
***************************************************************************/

Init ==
    /\ LastHash = NoHash
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ Received = [n \in Node |-> {}]

(***************************************************************************)
(*  HELPERS                                                               *)
***************************************************************************/

(* The public key belonging to a node, obtained via its private key *)
PubKey(n) == PubKeyOfPriv(Owner[n])

(* The data that is signed for a block – abstracted as a sequence *)
BlockData(b) == << b.type, b.account, b.prevHash, b.amount,
                  b.recipient, b.representative >>

(* Predicate that a block's signature is correct for its account *)
SignatureOK(b) ==
    LET pk == b.account
        priv == CHOOSE p \in PrivateKey : PubKeyOfPriv(p) = pk
    IN Verify(pk, BlockData(b), b.signature)

(* The balance of an account as computed by walking its chain.
   For simplicity we define it recursively on the ledger of a *single*
   node (the invariant holds for every node). *)
Balance(node, acc, h) ==
    IF h = NoHash THEN 0
    ELSE
        LET blk == Ledger[node][h] IN
        CASE blk.type = "genesis" -> blk.amount
         [] blk.type = "send"    -> Balance(node, acc, blk.prevHash) - blk.amount
         [] blk.type = "receive"-> Balance(node, acc, blk.prevHash) + blk.amount
         [] blk.type = "open"   -> blk.amount
         [] blk.type = "change" -> Balance(node, acc, blk.prevHash)
         [] OTHER               -> Balance(node, acc, blk.prevHash)

(*  Checks that a send block does not overdraft its account. *)
SendOK(node, b) ==
    /\ b.type = "send"
    /\ b.prevHash # NoHash
    /\ Balance(node, b.account, b.prevHash) >= b.amount

(*  Checks that an open block references an existing send block that
    targets its public key. *)
OpenOK(node, b) ==
    /\ b.type = "open"
    /\ \E h \in Hash :
        /\ Ledger[node][h] # NoBlock
        /\ Ledger[node][h].type = "send"
        /\ Ledger[node][h].recipient = b.account
        /\ b.prevHash = h

(*  Checks that a receive block references a send block that has not yet
    been received. *)
ReceiveOK(node, b) ==
    /\ b.type = "receive"
    /\ \E h \in Hash :
        /\ Ledger[node][h] # NoBlock
        /\ Ledger[node][h].type = "send"
        /\ Ledger[node][h].recipient = b.account
        /\ b.prevHash = b.prevHash   \* (prevHash of the receiver's own chain)
        /\ b.amount = Ledger[node][h].amount

(*  Checks that a change block simply references the previous block. *)
ChangeOK(node, b) ==
    /\ b.type = "change"
    /\ b.prevHash # NoHash

(*  General validity test for a newly created block before it is
    broadcast. *)
BlockWellFormed(node, b) ==
    /\ SignatureOK(b)
    /\ CASE b.type = "genesis" -> TRUE
        [] b.type = "send"    -> SendOK(node, b)
        [] b.type = "open"    -> OpenOK(node, b)
        [] b.type = "receive"-> ReceiveOK(node, b)
        [] b.type = "change" -> ChangeOK(node, b)
        [] OTHER              -> FALSE

(***************************************************************************)
(*  ACTIONS                                                               *)
***************************************************************************)

(* 1. Create the genesis block – can happen only once *)
CreateGenesis ==
    /\ LastHash = NoHash
    /\ \E n \in Node :
        LET pk == PubKey(n)
            b  == [ type          |-> "genesis",
                    account       |-> pk,
                    prevHash      |-> NoHash,
                    amount        |-> GenesisBalance,
                    recipient     |-> NoPublicKey,
                    representative|-> NoPublicKey,
                    signature     |-> Sign(Owner[n], BlockData([type |-> "genesis", account |-> pk,
                                                                prevHash |-> NoHash, amount |-> GenesisBalance,
                                                                recipient |-> NoPublicKey, representative |-> NoPublicKey]))
                  ]
            newHash == CalculateHashImpl(b, NoHash)
        IN /\ SignatureOK(b)
           /\ LastHash' = newHash
           /\ Ledger' = [m \in Node |-> [h \in Hash |-> IF h = newHash THEN b ELSE Ledger[m][h]]]
           /\ Received' = [m \in Node |-> {}]
           /\ UNCHANGED << >>

(* 2. Create a generic block (send, open, receive, change) *)
CreateBlock ==
    /\ LastHash # NoHash
    /\ \E n \in Node, b \in Block :
        /\ b.prevHash = LastHash
        /\ BlockWellFormed(n, b)
        /\ LET newHash == CalculateHashImpl(b, LastHash)
           IN /\ LastHash' = newHash
              /\ Ledger' = Ledger               \* ledger unchanged until validation
              /\ Received' = [m \in Node |-> Received[m] \cup {b}]
              /\ UNCHANGED LastHash   \* (already updated above)

(* 3. Process a received block at a node – validate and add to ledger *)
ProcessBlock ==
    /\ \E n \in Node, b \in Received[n] :
        /\ SignatureOK(b)
        /\ (* reference checks – simplified *)
           IF b.type = "send" THEN
               /\ b.prevHash = LastHash   \* must follow the chain
               /\ SendOK(n, b)
           ELSE IF b.type = "open" THEN
               /\ OpenOK(n, b)
           ELSE IF b.type = "receive" THEN
               /\ ReceiveOK(n, b)
           ELSE IF b.type = "change" THEN
               /\ ChangeOK(n, b)
           ELSE TRUE
        /\ LET newHash == CalculateHashImpl(b, b.prevHash)
           IN /\ Ledger' = [m \in Node |-> [h \in Hash |->
                     IF h = newHash THEN b ELSE Ledger[m][h]]]
              /\ Received' = [m \in Node |-> IF m = n THEN Received[m] \ {b} ELSE Received[m]]
              /\ UNCHANGED LastHash

(* 4. No‑op (stutter) *)
Stutter ==
    /\ UNCHANGED << LastHash, Ledger, Received >>

Next ==
    \/ CreateGenesis
    \/ CreateBlock
    \/ ProcessBlock
    \/ Stutter

(***************************************************************************)
(*  SPECIFICATION                                                          *)
***************************************************************************)

Spec ==
    Init /\ [][Next]_<<LastHash, Ledger, Received>>

(***************************************************************************)
(*  INVARIANTS                                                             *)
***************************************************************************)

TypeInvariant ==
    /\ LastHash \in Hash
    /\ Ledger \in [Node -> [Hash -> Block]]
    /\ Received \in [Node -> SUBSET Block]

SafetyInvariant ==
    /\ \A n \in Node : \A h \in Hash :
          (Ledger[n][h] # NoBlock) => SignatureOK(Ledger[n][h])

(***************************************************************************)
(*  THE LIST OF INVARIANTS THAT TLC SHOULD CHECK                           *)
***************************************************************************)

INVARIANT TypeInvariant
INVARIANT SafetyInvariant

=============================================================================