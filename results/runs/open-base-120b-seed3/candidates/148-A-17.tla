---- MODULE Nano ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Hash,          \* Set of all possible block hashes
    NoHashVal,     \* Sentinel hash value indicating no hash
    PrivateKey,    \* Set of private keys
    PublicKey,     \* Set of public keys
    Node,          \* Set of network nodes
    GenesisBalance,\* Total supply of coins at genesis
    NoBlockVal,    \* Sentinel block value indicating absence of a block
    CalculateHash, \* Abstract hash‑calculation operator (will be overridden)
    NoHash,        \* Alias for NoHashVal
    NoBlock        \* Alias for NoBlockVal

\* ----------------------------------------------------------------------
\* Aliases for readability
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* Types used in the specification
Sig == [owner : PublicKey, data : STRING]

Block == [
    type    : {"Genesis", "Send", "Open", "Receive", "Change"},
    prev    : Hash,
    account : PublicKey,
    data    : STRING,
    sig     : Sig
]

\* ----------------------------------------------------------------------
\* Constant mappings that the modeler must supply
\* (they are declared as constants but not listed in the required identifiers;
\*  their existence is assumed for the specification to be meaningful.)
PrivToPub \in [PrivateKey -> PublicKey]   \* private‑key → public‑key map
NodeKey   \in [Node -> PrivateKey]        \* which private key a node owns

\* ----------------------------------------------------------------------
\* Variables
VARIABLES
    LastHash,   \* The most recently calculated block hash
    Ledger,     \* [Node -> [Hash -> Block]]  each node’s copy of the ledger
    Received    \* [Node -> SUBSET Hash]       blocks pending validation

\* ----------------------------------------------------------------------
\* Helper operator to produce a deterministic “signature”
Sign(pk, msg) == [owner |-> PrivToPub[pk], data |-> msg]

\* ----------------------------------------------------------------------
\* Helper operator that checks a block’s signature against its account
ValidSignature(b) == b.sig.owner = b.account

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ LastHash = NoHash
    /\ Ledger   = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ Received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Action: create the genesis block (may happen only once)
CreateGenesis ==
    /\ LastHash = NoHash
    /\ \E n \in Node :
          LET pk == NodeKey[n] IN
          LET balStr == "genesis:" \o ToString(GenesisBalance) IN
          LET b == [
                type    |-> "Genesis",
                prev    |-> NoHash,
                account |-> PrivToPub[pk],
                data    |-> balStr,
                sig     |-> Sign(pk, balStr)
          ] IN
          LET h == CalculateHash(b, NoHash) IN
          /\ LastHash' = h
          /\ Ledger' = [n' \in Node |-> [Ledger[n'] EXCEPT ![h] = b]]
          /\ Received' = Received
          /\ UNCHANGED << >>
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create a non‑genesis block of an arbitrary allowed type
CreateBlock ==
    /\ LastHash # NoHash    \* genesis must already exist
    /\ \E n \in Node :
          LET pk == NodeKey[n] IN
          \E btype \in {"Send","Open","Receive","Change"} :
              LET payload ==
                  CASE btype = "Send"    -> "send:" \o ToString(GenesisBalance)
                       [] btype = "Open"    -> "open"
                       [] btype = "Receive" -> "receive"
                       [] btype = "Change"  -> "change"
              IN
              LET b == [
                    type    |-> btype,
                    prev    |-> LastHash,
                    account |-> PrivToPub[pk],
                    data    |-> payload,
                    sig     |-> Sign(pk, payload)
              ] IN
              LET h == CalculateHash(b, LastHash) IN
              /\ LastHash' = h
              /\ Ledger' = [n' \in Node |-> [Ledger[n'] EXCEPT ![h] = b]]
              /\ Received' = [n' \in Node |-> Received[n'] \cup {h}]
              /\ UNCHANGED << >>
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
Next == 
    \/ CreateGenesis
    \/ CreateBlock

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ LastHash \in Hash
    /\ Ledger \in [Node -> [Hash -> Block]]
    /\ Received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Safety invariant: every block stored in any ledger has a valid signature
SafetyInvariant ==
    \A n \in Node :
        \A h \in DOMAIN Ledger[n] :
            LET b == Ledger[n][h] IN
            b # NoBlock => ValidSignature(b)

\* ----------------------------------------------------------------------
\* The operator that the .cfg file substitutes for CalculateHash
CalculateHashImpl(b, prev) == NoHashVal   \* placeholder implementation

=============================================================================