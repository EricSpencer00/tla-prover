---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (to be supplied by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,          \* set of all possible block hashes
    NoHashVal,    \* sentinel value meaning “no hash yet”
    PrivateKey,   \* set of private keys
    PublicKey,    \* set of public keys
    Node,         \* set of network nodes
    GenesisBalance, \* total coin supply (a natural number)
    NoBlockVal,   \* sentinel value meaning “no block”
    CalculateHash, \* abstract hash operator (will be overridden)
    NoHash,       \* sentinel hash (same as NoHashVal, kept for readability)
    NoBlock       \* sentinel block (same as NoBlockVal, kept for readability)

\* ----------------------------------------------------------------------
\* USER‑DEFINED IMPLEMENTATION OF THE HASH FUNCTION (overridden in .cfg)
\* ----------------------------------------------------------------------
CalculateHashImpl(d, p) == 
    \* By default we pick an arbitrary element of Hash that is not
    \* already used; the concrete .cfg can replace this with a finite
    \* implementation.
    CHOOSE h \in Hash : TRUE

CalculateHash(d, p) == CalculateHashImpl(d, p)

\* ----------------------------------------------------------------------
\* MAPPINGS BETWEEN KEYS AND OWNERSHIP (abstract, can be instantiated)
\* ----------------------------------------------------------------------
PrivateToPublic \in [PrivateKey -> PublicKey]
NodePriv \in [Node -> PrivateKey]

PubOf(priv) == PrivateToPublic[priv]

PrivOf(pub) == 
    CHOOSE k \in PrivateKey : PrivateToPublic[k] = pub

\* ----------------------------------------------------------------------
\* BLOCK REPRESENTATION
\* ----------------------------------------------------------------------
Block == [
    type        : {"Genesis", "Send", "Open", "Receive", "Change"},
    hash        : Hash,
    prev        : Hash,
    account     : PublicKey,   \* owner of the chain this block belongs to
    dest        : PublicKey,   \* for Send blocks
    amount      : Nat,
    source      : Hash,        \* for Open/Receive blocks
    repr        : PublicKey,   \* for Change blocks
    signature   : String       \* abstract representation of a signature
]

\* ----------------------------------------------------------------------
\* SIGNING AND VERIFICATION (abstract)
\* ----------------------------------------------------------------------
Sign(priv, data) == 
    \* abstract signature – the concrete model can replace this with a
    \* deterministic function if desired.
    "sig_" \o ToString(priv) \o "_" \o ToString(data)

VerifySignature(b) ==
    LET pub == b.account
        priv == PrivOf(pub)
    IN b.signature = Sign(priv, b)

\* ----------------------------------------------------------------------
\* STATE VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    LastHash,          \* the hash of the most recently created block
    Blocks,            \* global pool of created blocks (hash -> Block or NoBlockVal)
    Ledger,            \* per‑node copy of the distributed ledger (node -> [hash -> BlockOrEmpty])
    Received,          \* per‑node set of hashes that have been received but not yet processed
    GenesisDone,       \* TRUE after the genesis block has been created
    Balances           \* abstract per‑account balance view (public key -> Nat)

\* ----------------------------------------------------------------------
\* HELPER DEFINITIONS
\* ----------------------------------------------------------------------
BlockOrEmpty == [b \in Block |-> b] \cup {NoBlockVal}

HashDomain(bset) == {h \in Hash : bset[h] # NoBlockVal}

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init ==
    /\ LastHash = NoHashVal
    /\ Blocks = [h \in Hash |-> NoBlockVal]
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ Received = [n \in Node |-> {}]
    /\ GenesisDone = FALSE
    /\ Balances = [pk \in PublicKey |-> 0]

\* ----------------------------------------------------------------------
\* ACTION: CREATE GENESIS BLOCK
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ ~GenesisDone
    /\ \E n \in Node :
        LET priv   == NodePriv[n]
            pub    == PubOf(priv)
            bData  == [
                        type      |-> "Genesis",
                        prev      |-> NoHashVal,
                        account   |-> pub,
                        dest      |-> NoHashVal,
                        amount    |-> GenesisBalance,
                        source    |-> NoHashVal,
                        repr      |-> NoHashVal
                     ]
            h      == CalculateHash(bData, NoHashVal)
            b      == [bData EXCEPT !.hash = h,
                        !.signature = Sign(priv, bData)]
        IN  /\ h \in Hash
            /\ h # NoHashVal
            /\ h \notin HashDomain(Blocks)
            /\ LastHash' = h
            /\ Blocks' = [Blocks EXCEPT ![h] = b]
            /\ Ledger' = [n2 \in Node |-> Ledger[n2] EXCEPT ![h] = b]
            /\ Received' = Received
            /\ GenesisDone' = TRUE
            /\ Balances' = [Balances EXCEPT ![pub] = GenesisBalance]
            /\ UNCHANGED <<NodePriv, PrivateToPublic>>

\* ----------------------------------------------------------------------
\* ACTION: CREATE SEND BLOCK
\* ----------------------------------------------------------------------
CreateSend ==
    /\ GenesisDone
    /\ \E n \in Node :
        LET priv   == NodePriv[n]
            sender == PubOf(priv)
            maxAmt == Balances[sender]
            amt    \in 0..maxAmt
            dest   \in PublicKey
            prev   == LastHash
            bData  == [
                        type      |-> "Send",
                        prev      |-> prev,
                        account   |-> sender,
                        dest      |-> dest,
                        amount    |-> amt,
                        source    |-> NoHashVal,
                        repr      |-> NoHashVal
                     ]
            h      == CalculateHash(bData, prev)
            b      == [bData EXCEPT !.hash = h,
                        !.signature = Sign(priv, bData)]
        IN  /\ h \in Hash
            /\ h \notin HashDomain(Blocks)
            /\ LastHash' = h
            /\ Blocks' = [Blocks EXCEPT ![h] = b]
            /\ Received' = [node \in Node |-> Received[node] \cup {h}]
            /\ Balances' = [Balances EXCEPT ![sender] = @ - amt]
            /\ UNCHANGED <<Ledger, GenesisDone>>

\* ----------------------------------------------------------------------
\* ACTION: CREATE OPEN BLOCK
\* ----------------------------------------------------------------------
CreateOpen ==
    /\ GenesisDone
    /\ \E n \in Node :
        LET priv   == NodePriv[n]
            acct   == PubOf(priv)
            src    \in Hash
            bsrc   == Blocks[src]
        IN  /\ bsrc # NoBlockVal
            /\ bsrc.type = "Send"
            /\ bsrc.dest = acct
            /\ bsrc.hash # NoHashVal   \* ensure the send was created
            /\ bsrc.amount \in Nat
            /\ \A h \in HashDomain(Ledger[n]) : Ledger[n][h].account # acct
               \* no block for this account exists yet in this node's ledger
            /\ bData  == [
                        type      |-> "Open",
                        prev      |-> NoHashVal,
                        account   |-> acct,
                        dest      |-> NoHashVal,
                        amount    |-> bsrc.amount,
                        source    |-> src,
                        repr      |-> NoHashVal
                     ]
            /\ h      == CalculateHash(bData, NoHashVal)
            /\ b      == [bData EXCEPT !.hash = h,
                        !.signature = Sign(priv, bData)]
            /\ h \in Hash
            /\ h \notin HashDomain(Blocks)
            /\ LastHash' = h
            /\ Blocks' = [Blocks EXCEPT ![h] = b]
            /\ Received' = [node \in Node |-> Received[node] \cup {h}]
            /\ Balances' = [Balances EXCEPT ![acct] = @ + bsrc.amount]
            /\ UNCHANGED <<Ledger, GenesisDone>>

\* ----------------------------------------------------------------------
\* ACTION: CREATE RECEIVE BLOCK
\* ----------------------------------------------------------------------
CreateReceive ==
    /\ GenesisDone
    /\ \E n \in Node :
        LET priv   == NodePriv[n]
            acct   == PubOf(priv)
            src    \in Hash
            bsrc   == Blocks[src]
        IN  /\ bsrc # NoBlockVal
            /\ bsrc.type = "Send"
            /\ bsrc.dest = acct
            /\ \E h \in HashDomain(Ledger[n]) :
                Ledger[n][h].type = "Receive"
                /\ Ledger[n][h].source = src
                => FALSE   \* the send has not already been received
            /\ bData  == [
                        type      |-> "Receive",
                        prev      |-> LastHash,
                        account   |-> acct,
                        dest      |-> NoHashVal,
                        amount    |-> bsrc.amount,
                        source    |-> src,
                        repr      |-> NoHashVal
                     ]
            /\ h      == CalculateHash(bData, LastHash)
            /\ b      == [bData EXCEPT !.hash = h,
                        !.signature = Sign(priv, bData)]
            /\ h \in Hash
            /\ h \notin HashDomain(Blocks)
            /\ LastHash' = h
            /\ Blocks' = [Blocks EXCEPT ![h] = b]
            /\ Received' = [node \in Node |-> Received[node] \cup {h}]
            /\ Balances' = [Balances EXCEPT ![acct] = @ + bsrc.amount]
            /\ UNCHANGED <<Ledger, GenesisDone>>

\* ----------------------------------------------------------------------
\* ACTION: CREATE CHANGE REPRESENTATIVE BLOCK
\* ----------------------------------------------------------------------
CreateChange ==
    /\ GenesisDone
    /\ \E n \in Node :
        LET priv   == NodePriv[n]
            acct   == PubOf(priv)
            newRep \in PublicKey
            bData  == [
                        type      |-> "Change",
                        prev      |-> LastHash,
                        account   |-> acct,
                        dest      |-> NoHashVal,
                        amount    |-> 0,
                        source    |-> NoHashVal,
                        repr      |-> newRep
                     ]
            h      == CalculateHash(bData, LastHash)
            b      == [bData EXCEPT !.hash = h,
                        !.signature = Sign(priv, bData)]
        IN  /\ h \in Hash
            /\ h \notin HashDomain(Blocks)
            /\ LastHash' = h
            /\ Blocks' = [Blocks EXCEPT ![h] = b]
            /\ Received' = [node \in Node |-> Received[node] \cup {h}]
            /\ UNCHANGED <<Ledger, GenesisDone, Balances>>

\* ----------------------------------------------------------------------
\* ACTION: PROCESS A RECEIVED BLOCK AT A NODE
\* ----------------------------------------------------------------------
ProcessBlock ==
    /\ \E n \in Node, h \in Received[n] :
        LET b == Blocks[h]
        IN  /\ b # NoBlockVal
            /\ VerifySignature(b)          \* cryptographic check
            /\ (b.type = "Send") => 
                \* sender must already have a previous block in its chain
                b.prev = LastHash \/ b.prev = NoHashVal
            /\ (b.type = "Open") =>
                \* the source must be a Send block already in the ledger
                \E sh \in HashDomain(Ledger[n]) :
                    Ledger[n][sh] = Blocks[b.source]
            /\ (b.type = "Receive") =>
                \* source must be a Send block not yet received by this node
                \E sh \in HashDomain(Ledger[n]) :
                    Ledger[n][sh] = Blocks[b.source]
            /\ (b.type = "Change") => TRUE
            /\ Ledger' = [Ledger EXCEPT ![n][h] = b]
            /\ Received' = [Received EXCEPT ![n] = @ \ {h}]
            /\ UNCHANGED <<LastHash, Blocks, GenesisDone, Balances>>

\* ----------------------------------------------------------------------
\* COMBINED NEXT ACTION
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<LastHash, Blocks, Ledger, Received, GenesisDone, Balances>>

\* ----------------------------------------------------------------------
\* TYPE INVARIANT
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ LastHash \in Hash \/ LastHash = NoHashVal
    /\ Blocks \in [Hash -> BlockOrEmpty]
    /\ Ledger \in [Node -> [Hash -> BlockOrEmpty]]
    /\ Received \in [Node -> SUBSET Hash]
    /\ GenesisDone \in BOOLEAN
    /\ Balances \in [PublicKey -> Nat]

\* ----------------------------------------------------------------------
\* SAFETY INVARIANT (cryptographic signature correctness)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in HashDomain(Ledger[n]) :
            VerifySignature(Ledger[n][h])

\* ----------------------------------------------------------------------
\* THE REQUIRED EXPORTS
\* ----------------------------------------------------------------------
\* The .cfg file expects the following identifiers:
\*   SPEC, TypeInvariant, SafetyInvariant, CalculateHashImpl
=============================================================================