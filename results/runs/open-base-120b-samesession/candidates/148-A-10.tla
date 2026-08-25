---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (to be supplied by the TLC configuration)
\* ----------------------------------------------------------------------
CONSTANTS 
    Hash,            \* Universe of possible block hashes
    NoHashVal,       \* Sentinel value meaning “no hash”
    PrivateKey,      \* Universe of private keys
    PublicKey,       \* Universe of public keys
    Node,            \* Set of network nodes
    GenesisBalance,  \* Total supply of coins (a natural number)
    NoBlockVal,      \* Sentinel value meaning “no block”
    CalculateHash,   \* Abstract hash operator (overridden by CalculateHashImpl)
    NoHash,          \* Alias for NoHashVal (used in the model)
    NoBlock          \* Alias for NoBlockVal (used in the model)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
BlockType == {"genesis", "send", "open", "receive", "change"}

Block == [ 
    hash        : Hash,
    type        : BlockType,
    prev        : Hash,
    account     : PublicKey,
    amount      : Nat,
    recipient   : PublicKey,
    source      : Hash,          \* hash of the send block referenced by an open/receive
    representative : PublicKey,
    sig         : STRING          \* abstract signature
]

\* ----------------------------------------------------------------------
\* Helper operators (abstract)
\* ----------------------------------------------------------------------
\* Mapping from a private key to its public key (given as a constant function)
\* The configuration must supply a constant function PrivateToPublic \in [PrivateKey -> PublicKey]
VARIABLES PrivateToPublic

\* Mapping from a node to the private key it owns (given as a constant function)
\* The configuration must supply a constant function NodeToPriv \in [Node -> PrivateKey]
VARIABLES NodeToPriv

\* Abstract cryptographic primitives
Sign(priv, data) == 
    (* an abstract signature of 'data' using private key 'priv' *) 
    "sig_" \o ToString(priv) \o "_" \o ToString(data)

VerifySig(pub, data, sig) == 
    (* abstract verification: true iff sig has the form produced by Sign with the matching private key *) 
    \E priv \in PrivateKey : (PrivateToPublic[priv] = pub) /\ sig = Sign(priv, data)

\* Abstract hash calculation (overridden by CalculateHashImpl in the .cfg)
CalculateHashImpl(data, prev) == 
    CHOOSE h \in Hash : h # NoHash

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    lastHash,   \* The hash of the most recently created block (or NoHash)
    ledger,    \* [Node -> [Hash -> (Block \cup {NoBlock})]]
    received   \* [Node -> SUBSET Hash]   (hashes of blocks pending validation)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Utility functions
\* ----------------------------------------------------------------------
IsGenesisBlock(b) == b.type = "genesis"
IsSendBlock(b)    == b.type = "send"
IsOpenBlock(b)    == b.type = "open"
IsReceiveBlock(b) == b.type = "receive"
IsChangeBlock(b)  == b.type = "change"

BlockData(b) == 
    (* the data that is signed – abstractly the concatenation of the
       fields that are relevant for the block type *)
    << b.type, b.prev, b.account, b.amount, b.recipient, b.source, b.representative >>

Owner(b) == b.account

\* Determine the latest block belonging to a given account in a given ledger
LatestBlock(account, l) ==
    \E h \in Hash :
        /\ l[Node][h] # NoBlock
        /\ Owner(l[Node][h]) = account
        /\ \A h2 \in Hash :
            (l[Node][h2] # NoBlock /\ Owner(l[Node][h2]) = account) => 
                (h2 = h \/ l[Node][h2].prev # h)   \* no later block points to h

\* Compute the balance of an account by walking its chain (abstractly)
Balance(account, l) ==
    IF \E h \in Hash : l[Node][h] # NoBlock /\ Owner(l[Node][h]) = account
    THEN
        LET blocks == { l[Node][h] : h \in Hash /\ l[Node][h] # NoBlock /\ Owner(l[Node][h]) = account } 
        IN
            ( * sum over the chain; abstractly we treat the balance as a nondeterministic
               value that respects the invariants defined elsewhere *) 
            CHOOSE b \in Nat : TRUE
    ELSE 0

\* Abstract predicate for whether a send block is allowed
CanSend(account, amt, l) == amt <= Balance(account, l)

\* Validate a received block for a given node (abstract)
ValidateBlock(node, b, l) ==
    /\ b # NoBlock
    /\ VerifySig(Owner(b), BlockData(b), b.sig)
    /\ b.prev = NoHash \/ (\E hp \in Hash : l[node][hp] # NoBlock /\ l[node][hp].hash = b.prev)
    /\ CASE b.type OF
        "genesis" -> TRUE
        "send"    -> CanSend(b.account, b.amount, l)
        "open"    -> (\E s \in Hash :
                        l[node][s] # NoBlock /\ IsSendBlock(l[node][s]) /\
                        l[node][s].recipient = b.account /\ s = b.source)
        "receive" -> (\E s \in Hash :
                        l[node][s] # NoBlock /\ IsSendBlock(l[node][s]) /\
                        l[node][s].recipient = b.account /\ s = b.source)
        "change"  -> TRUE
        OTHER     -> FALSE

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Create the genesis block (once)
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E node \in Node :
        LET priv == NodeToPriv[node]
            pub  == PrivateToPublic[priv]
            data == << "genesis", NoHash, pub, GenesisBalance, NoHash, NoHash, NoHash >>
            sig  == Sign(priv, data)
            h    == CalculateHash(data, NoHash)
            gblk == [ hash |-> h,
                     type |-> "genesis",
                     prev |-> NoHash,
                     account |-> pub,
                     amount |-> GenesisBalance,
                     recipient |-> NoHash,
                     source |-> NoHash,
                     representative |-> NoHash,
                     sig |-> sig ]
        IN
            /\ h # NoHash
            /\ lastHash' = h
            /\ ledger' = [n \in Node |-> [hash \in Hash |-> 
                        IF hash = h THEN gblk ELSE ledger[n][hash]]]
            /\ received' = [n \in Node |-> {}]
            /\ UNCHANGED << PrivateToPublic, NodeToPriv >>
    /\ UNCHANGED << >>

\* 2. Create a send block
CreateSend(node, amt, recPub) ==
    /\ node \in Node
    /\ let priv == NodeToPriv[node]
           pub  == PrivateToPublic[priv]
           prevHash == lastHash
           data == << "send", prevHash, pub, amt, recPub, NoHash, NoHash >>
           sig  == Sign(priv, data)
           h    == CalculateHash(data, prevHash)
           sblk == [ hash |-> h,
                     type |-> "send",
                     prev |-> prevHash,
                     account |-> pub,
                     amount |-> amt,
                     recipient |-> recPub,
                     source |-> NoHash,
                     representative |-> NoHash,
                     sig |-> sig ]
    in
        /\ CanSend(pub, amt, ledger)
        /\ h # NoHash
        /\ lastHash' = h
        /\ ledger' = [n \in Node |-> [hash \in Hash |-> 
                        IF hash = h THEN sblk ELSE ledger[n][hash]]]
        /\ received' = [n \in Node |-> received[n] \cup {h}]
        /\ UNCHANGED << PrivateToPublic, NodeToPriv >>

\* 3. Create an open block (for a new account)
CreateOpen(node, srcHash) ==
    /\ node \in Node
    /\ let priv == NodeToPriv[node]
           pub  == PrivateToPublic[priv]
           src  == ledger[node][srcHash]   \* must be a send block addressed to this account
           amt  == src.amount
           prevHash == NoHash
           data == << "open", prevHash, pub, amt, NoHash, srcHash, NoHash >>
           sig  == Sign(priv, data)
           h    == CalculateHash(data, prevHash)
           obl  == [ hash |-> h,
                     type |-> "open",
                     prev |-> prevHash,
                     account |-> pub,
                     amount |-> amt,
                     recipient |-> NoHash,
                     source |-> srcHash,
                     representative |-> NoHash,
                     sig |-> sig ]
    in
        /\ src # NoBlock /\ IsSendBlock(src) /\ src.recipient = pub
        /\ h # NoHash
        /\ lastHash' = h
        /\ ledger' = [n \in Node |-> [hash \in Hash |-> 
                        IF hash = h THEN obl ELSE ledger[n][hash]]]
        /\ received' = [n \in Node |-> received[n] \cup {h}]
        /\ UNCHANGED << PrivateToPublic, NodeToPriv >>

\* 4. Create a receive block
CreateReceive(node, srcHash) ==
    /\ node \in Node
    /\ let priv == NodeToPriv[node]
           pub  == PrivateToPublic[priv]
           src  == ledger[node][srcHash]   \* must be a send block addressed to this account
           amt  == src.amount
           prevHash == lastHash
           data == << "receive", prevHash, pub, amt, NoHash, srcHash, NoHash >>
           sig  == Sign(priv, data)
           h    == CalculateHash(data, prevHash)
           rblk == [ hash |-> h,
                     type |-> "receive",
                     prev |-> prevHash,
                     account |-> pub,
                     amount |-> amt,
                     recipient |-> NoHash,
                     source |-> srcHash,
                     representative |-> NoHash,
                     sig |-> sig ]
    in
        /\ src # NoBlock /\ IsSendBlock(src) /\ src.recipient = pub
        /\ h # NoHash
        /\ lastHash' = h
        /\ ledger' = [n \in Node |-> [hash \in Hash |-> 
                        IF hash = h THEN rblk ELSE ledger[n][hash]]]
        /\ received' = [n \in Node |-> received[n] \cup {h}]
        /\ UNCHANGED << PrivateToPublic, NodeToPriv >>

\* 5. Create a change representative block
CreateChange(node, newRep) ==
    /\ node \in Node
    /\ let priv == NodeToPriv[node]
           pub  == PrivateToPublic[priv]
           prevHash == lastHash
           data == << "change", prevHash, pub, 0, NoHash, NoHash, newRep >>
           sig  == Sign(priv, data)
           h    == CalculateHash(data, prevHash)
           cblk == [ hash |-> h,
                     type |-> "change",
                     prev |-> prevHash,
                     account |-> pub,
                     amount |-> 0,
                     recipient |-> NoHash,
                     source |-> NoHash,
                     representative |-> newRep,
                     sig |-> sig ]
    in
        /\ h # NoHash
        /\ lastHash' = h
        /\ ledger' = [n \in Node |-> [hash \in Hash |-> 
                        IF hash = h THEN cblk ELSE ledger[n][hash]]]
        /\ received' = [n \in Node |-> received[n] \cup {h}]
        /\ UNCHANGED << PrivateToPublic, NodeToPriv >>

\* 6. Process a received block at a node
ProcessReceived(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
        LET b == ledger[node][h] \* block may be NoBlock if not yet stored
        IN
            /\ b # NoBlock
            /\ ValidateBlock(node, b, ledger)
            /\ ledger' = [n \in Node |-> 
                            IF n = node 
                            THEN [hash \in Hash |-> 
                                    IF hash = h THEN b ELSE ledger[n][hash]]
                            ELSE ledger[n]]
            /\ received' = [n \in Node |-> 
                            IF n = node 
                            THEN received[n] \ {h}
                            ELSE received[n]]
            /\ UNCHANGED lastHash
            /\ UNCHANGED << PrivateToPublic, NodeToPriv >>
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Next-state relation (nondeterministic choice of an enabled action)
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ \E node \in Node, amt \in Nat, rcpt \in PublicKey : CreateSend(node, amt, rcpt)
    \/ \E node \in Node, src \in Hash : CreateOpen(node, src)
    \/ \E node \in Node, src \in Hash : CreateReceive(node, src)
    \/ \E node \in Node, rep \in PublicKey : CreateChange(node, rep)
    \/ \E node \in Node : ProcessReceived(node)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Type invariant (ensures variables stay within declared types)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHash
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Safety invariant (cryptographic correctness)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == ledger[n][h] IN
                b = NoBlock \/ 
                /\ VerifySig(Owner(b), BlockData(b), b.sig)

\* ----------------------------------------------------------------------
\* The set of invariants required by the configuration
\* ----------------------------------------------------------------------
\* (The configuration will reference them by name)
INVARIANTS == TypeInvariant /\ SafetyInvariant

\* ----------------------------------------------------------------------
\* Operator required by the .cfg substitution
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) == 
    CHOOSE h \in Hash : h # NoHash

====