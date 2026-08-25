---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* CONSTANTS
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,               \* Set of all possible block hashes
    NoHashVal,          \* Sentinel value not in Hash, denotes "no hash"
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,    \* Total amount of coins created in the genesis block
    NoBlockVal,         \* Sentinel value not in Block, denotes "no block"
    CalculateHash,      \* Abstract hash calculation operator (overridden)
    NoHash,             \* Alias for NoHashVal (provided for cfg substitution)
    NoBlock             \* Alias for NoBlockVal (provided for cfg substitution)

\* ----------------------------------------------------------------------
\* TYPES AND AUXILIARY DEFINITIONS
\* ----------------------------------------------------------------------
Sig == 1..1000               \* Abstract type for signatures (finite for model checking)

Block == [
    type       : {"genesis", "send", "receive", "open", "change"},
    prev       : Hash \/ {NoHashVal},
    src        : Hash \/ {NoHashVal},   \* referenced send block for receive/open
    dest       : PublicKey \/ {NoHashVal}, \* destination account (for send/open)
    amount     : Nat,
    rep        : PublicKey \/ {NoHashVal}, \* representative (for change)
    signer     : PublicKey,
    sig        : Sig
]

\* Mapping from a private key to its public key (abstract, fixed)
PrivateToPublic \in [PrivateKey -> PublicKey]

\* Mapping from each node to the private key it owns (abstract, fixed)
NodeKey \in [Node -> PrivateKey]

\* The public key belonging to the genesis account (chosen arbitrarily)
GenesisPub == CHOOSE pk \in PublicKey : TRUE

\* ----------------------------------------------------------------------
\* ABSTRACT CRYPTOGRAPHIC OPERATORS
\* ----------------------------------------------------------------------
Sign(priv, data) == CHOOSE s \in Sig : TRUE     \* returns a signature
VerifySig(pub, data, s) == TRUE                \* always succeeds (abstract)

\* ----------------------------------------------------------------------
\* STATE VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    LastHash,      \* The hash of the most recently created block (or NoHashVal)
    Ledger,        \* Ledger[node][hash] = block or NoBlockVal
    Received,      \* Received[node] = set of hashes pending validation
    AllBlocks      \* Global repository: AllBlocks[hash] = block or NoBlockVal

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init ==
    /\ LastHash = NoHashVal
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ Received = [n \in Node |-> {}]
    /\ AllBlocks = [h \in Hash |-> NoBlockVal]

\* ----------------------------------------------------------------------
\* HELPER FUNCTIONS
\* ----------------------------------------------------------------------
BlockHash(b) == CalculateHash(b, LastHash)    \* abstract hash calculation

ValidSignature(b) ==
    VerifySig(b.signer, b, b.sig)

\* Returns the most recent block owned by a given public key, if any.
\* For simplicity we scan all hashes; in a real spec this would be optimized.
LatestBlock(pub) ==
    CHOOSE h \in Hash :
        /\ Ledger[Node][h] # NoBlockVal
        /\ Ledger[Node][h].signer = pub
        /\ \A h2 \in Hash :
            (Ledger[Node][h2] # NoBlockVal /\ Ledger[Node][h2].signer = pub) =>
                (h2 = h) \/ (h2 # h)   \* nondeterministic choice; concrete ordering omitted

\* Computes the balance of an account by summing its receive amounts
\* and subtracting its send amounts (abstract, may over‑approximate).
AccountBalance(pub) ==
    LET recv == { b \in AllBlocks : b # NoBlockVal /\ b.type = "receive" /\ b.dest = pub }
        send == { b \in AllBlocks : b # NoBlockVal /\ b.type = "send"   /\ b.signer = pub }
    IN  (IF pub = GenesisPub THEN GenesisBalance ELSE 0)
        + Sum( recv, b |-> b.amount )
        - Sum( send , b |-> b.amount )

\* ----------------------------------------------------------------------
\* ACTIONS
\* ----------------------------------------------------------------------
GenesisCreate ==
    /\ LastHash = NoHashVal
    /\ \E priv \in PrivateKey :
        LET pub == PrivateToPublic[priv] IN
        /\ pub = GenesisPub
        LET b == [
                type   |-> "genesis",
                prev   |-> NoHashVal,
                src    |-> NoHashVal,
                dest   |-> GenesisPub,
                amount |-> GenesisBalance,
                rep    |-> NoHashVal,
                signer |-> GenesisPub,
                sig    |-> Sign(priv, "genesis")
            ] IN
        /\ hash == BlockHash(b)
        /\ hash \in Hash
        /\ AllBlocks' = [AllBlocks EXCEPT ![hash] = b]
        /\ LastHash' = hash
        /\ Received' = [n \in Node |-> {}]
        /\ Ledger' = [n \in Node |-> [h \in Hash |-> IF h = hash THEN b ELSE NoBlockVal]]
        /\ UNCHANGED << >>
        
SendCreate(node, destPub, amt) ==
    /\ node \in Node
    /\ destPub \in PublicKey
    /\ amt \in Nat
    /\ LET priv == NodeKey[node] IN
       LET pub  == PrivateToPublic[priv] IN
       /\ AccountBalance(pub) >= amt
       LET prevHash == LastHash IN
       LET b == [
                type   |-> "send",
                prev   |-> prevHash,
                src    |-> NoHashVal,
                dest   |-> destPub,
                amount |-> amt,
                rep    |-> NoHashVal,
                signer |-> pub,
                sig    |-> Sign(priv, "send")
            ] IN
       /\ hash == BlockHash(b)
       /\ hash \in Hash
       /\ AllBlocks' = [AllBlocks EXCEPT ![hash] = b]
       /\ LastHash' = hash
       /\ Received' = [n \in Node |-> Received[n] \cup {hash}]
       /\ UNCHANGED << Ledger, AllBlocks >>  \* Ledger will be updated when nodes process

OpenCreate(node, sendHash) ==
    /\ node \in Node
    /\ sendHash \in Hash
    /\ LET priv == NodeKey[node] IN
       LET pub  == PrivateToPublic[priv] IN
       LET sendBlock == AllBlocks[sendHash] IN
       /\ sendBlock # NoBlockVal
       /\ sendBlock.type = "send"
       /\ sendBlock.dest = pub
       LET b == [
                type   |-> "open",
                prev   |-> NoHashVal,
                src    |-> sendHash,
                dest   |-> pub,
                amount |-> sendBlock.amount,
                rep    |-> NoHashVal,
                signer |-> pub,
                sig    |-> Sign(priv, "open")
            ] IN
       /\ hash == BlockHash(b)
       /\ hash \in Hash
       /\ AllBlocks' = [AllBlocks EXCEPT ![hash] = b]
       /\ LastHash' = hash
       /\ Received' = [n \in Node |-> Received[n] \cup {hash}]
       /\ UNCHANGED << Ledger >>

ReceiveCreate(node, sendHash) ==
    /\ node \in Node
    /\ sendHash \in Hash
    /\ LET priv == NodeKey[node] IN
       LET pub  == PrivateToPublic[priv] IN
       LET sendBlock == AllBlocks[sendHash] IN
       /\ sendBlock # NoBlockVal
       /\ sendBlock.type = "send"
       /\ sendBlock.dest = pub
       LET b == [
                type   |-> "receive",
                prev   |-> LastHash,
                src    |-> sendHash,
                dest   |-> pub,
                amount |-> sendBlock.amount,
                rep    |-> NoHashVal,
                signer |-> pub,
                sig    |-> Sign(priv, "receive")
            ] IN
       /\ hash == BlockHash(b)
       /\ hash \in Hash
       /\ AllBlocks' = [AllBlocks EXCEPT ![hash] = b]
       /\ LastHash' = hash
       /\ Received' = [n \in Node |-> Received[n] \cup {hash}]
       /\ UNCHANGED << Ledger >>

ChangeRepCreate(node, newRep) ==
    /\ node \in Node
    /\ newRep \in PublicKey
    /\ LET priv == NodeKey[node] IN
       LET pub  == PrivateToPublic[priv] IN
       LET b == [
                type   |-> "change",
                prev   |-> LastHash,
                src    |-> NoHashVal,
                dest   |-> NoHashVal,
                amount |-> 0,
                rep    |-> newRep,
                signer |-> pub,
                sig    |-> Sign(priv, "change")
            ] IN
       /\ hash == BlockHash(b)
       /\ hash \in Hash
       /\ AllBlocks' = [AllBlocks EXCEPT ![hash] = b]
       /\ LastHash' = hash
       /\ Received' = [n \in Node |-> Received[n] \cup {hash}]
       /\ UNCHANGED << Ledger >>

\* ----------------------------------------------------------------------
\* PROCESSING OF RECEIVED BLOCKS
\* ----------------------------------------------------------------------
ProcessBlock(node) ==
    /\ node \in Node
    /\ \E h \in Received[node] :
        LET b == AllBlocks[h] IN
        /\ b # NoBlockVal
        /\ ValidSignature(b)
        /\ (b.type = "send" => 
                (* sender must have enough balance at creation time – abstracted *)
                TRUE)
        /\ (b.type = "open" => 
                (* open must reference an unclaimed send – abstracted *)
                TRUE)
        /\ (b.type = "receive" => 
                (* receive must reference an unclaimed send – abstracted *)
                TRUE)
        /\ (b.type = "change" => TRUE)
        /\ (b.type = "genesis" => TRUE)
        /\ LET ledger' == [Ledger EXCEPT ![node][h] = b] IN
           /\ Received' = [Received EXCEPT ![node] = Received[node] \ {h}]
           /\ UNCHANGED << LastHash, AllBlocks >>
           /\ Ledger' = ledger'

\* ----------------------------------------------------------------------
\* NEXT STATE RELATION
\* ----------------------------------------------------------------------
Next ==
    \/ \E node \in Node, dest \in PublicKey, amt \in Nat : SendCreate(node, dest, amt)
    \/ \E node \in Node, sendHash \in Hash : OpenCreate(node, sendHash)
    \/ \E node \in Node, sendHash \in Hash : ReceiveCreate(node, sendHash)
    \/ \E node \in Node, newRep \in PublicKey : ChangeRepCreate(node, newRep)
    \/ \E node \in Node : ProcessBlock(node)
    \/ GenesisCreate

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received, AllBlocks>>

\* ----------------------------------------------------------------------
\* INVARIANTS
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ LastHash \in Hash \/ LastHash = NoHashVal
    /\ Ledger \in [Node -> [Hash -> (Block \/ {NoBlockVal})]]
    /\ Received \in [Node -> SUBSET Hash]
    /\ AllBlocks \in [Hash -> (Block \/ {NoBlockVal})]

SafetyInvariant ==
    /\ \A n \in Node : \A h \in Hash :
          (Ledger[n][h] # NoBlockVal) => ValidSignature(Ledger[n][h])
    /\ \A h \in Hash :
          (AllBlocks[h] # NoBlockVal) => ValidSignature(AllBlocks[h])

\* ----------------------------------------------------------------------
\* CALCULATEHASH IMPLEMENTATION (to be substituted in the .cfg)
\* ----------------------------------------------------------------------
CalculateHashImpl(b, prev) ==
    CHOOSE h \in Hash : TRUE    \* Non‑deterministic finite hash for model checking

====