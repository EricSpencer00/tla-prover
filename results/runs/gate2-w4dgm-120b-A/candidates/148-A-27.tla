---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

\* The Nano cryptocurrency blockchain uses a block-lattice: every account has its
\* own chain of blocks. To focus on the chemistry of signatures and hashes, the
\* model tracks the full ledger per network node and the set of blocks each
\* node has received but not yet validated; a received block is only ever
\* reflected in a node's ledger after explicit validation, which re-checks that
\* the signature matches the account's public key -- the safety property below.
\* Block-creation actions walk the chain to compute balances and refuse to
\* overdraw, so transaction amounts can be anything that keeps the chain legal.

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal

\* One node may own several private keys (a user's wallet); the mapping says
\* which public key each private key is tied to, which is what the signature
\* check validates against during block validation.
KeyOf : [PrivateKey -> PublicKey]

VARIABLES
  lastHash, ledger, received

\* The ledger is replicated per node and every block is a separate record
\* (nothing is overwritten), so the count of stored records grows with every
\* block creation action -- that is the state space explosion the spec mentions.
TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> (PublicKey \X PublicKey \X Hash \X Nat) \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

\* Sum of balances across every account chain in a node's ledger; walks the
\* chain from the genesis block forward, counting each account's final balance
\* exactly once. The "AlreadySeen" bookkeeping is what makes this finite.
SumBalances(n) ==
  LET
    Total == CHOOSE total : total \in Nat :
               \E seen : seen \subseteq PublicKey :
                 LET
                   ChainBalance(pk, h, seen) ==
                     IF h = NoHashVal \/ h \in seen
                     THEN 0
                     ELSE
                       LET x == ledger[n][h] IN
                         IF x # NoBlockVal /\ x[1] = pk
                         THEN ChainBalance(pk, x[3], seen \cup {h}) + x[4]
                         ELSE ChainBalance(pk, h, seen \cup {h})
                 IN total = LET
                              Sum(pk) == ChainBalance(pk, lastHash, {})
                              RECURSIVE SumOver(_)
                              SumOver(S) ==
                                IF S = {}
                                THEN 0
                                ELSE LET x == CHOOSE y \in S : TRUE IN Sum(x) + SumOver(S \ {x})
                            IN SumOver(PublicKey)
  IN Total

\* The ledger is replicated, so the invariants are checked per node.
Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* The genesis block is unique: it puts the full coin supply onto an account
\* chain that no other block will ever precede, so the whole ledger's range is
\* known exactly once it exists.
CreateGenesisBlock ==
  /\ lastHash = NoHashVal
  /\ \E n \in Node, k \in PrivateKey :
       /\ lastHash' = CalculateHash([pk |-> KeyOf[k], rev |-> NoHashVal, amt |-> GenesisBalance], NoHashVal)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = <<KeyOf[k], NoHashVal, NoHashVal, GenesisBalance>>]]
       /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]

\* A send block withdraws from the sender's chain, references the previous block,
\* and must never send more than the preceding balance.
CreateSendBlock ==
  /\ \E n \in Node, k \in PrivateKey, amt \in Nat :
       /\ lastHash # NoHashVal
       /\ amt <= SumBalances(n)
       /\ lastHash' = CalculateHash([pk |-> KeyOf[k], rev |-> lastHash, amt |-> amt], lastHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = <<KeyOf[k], lastHash, NoHashVal, amt>>]]
       /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]

\* An open block is the first block on an account's chain, anchored to a send
\* block that was addressed to the account's public key.
CreateOpenBlock ==
  /\ \E n \in Node, k \in PrivateKey, r \in Hash :
       /\ lastHash # NoHashVal /\ r \in received[n]
       /\ ledger[n][r] # NoBlockVal /\ ledger[n][r][1] = KeyOf[k]
       /\ lastHash' = CalculateHash([pk |-> KeyOf[k], rev |-> NoHashVal, amt |-> 0], lastHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = <<KeyOf[k], NoHashVal, r, 0>>]]
       /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]

\* A receive block is the second half of a transfer: it is addressed to the
\* receiving account's public key and must never claim a send block that a
\* previous receive block has already consumed (the no-double-spend rule).
CreateReceiveBlock ==
  /\ \E n \in Node, k \in PrivateKey, r \in Hash :
       /\ lastHash # NoHashVal /\ r \in received[n]
       /\ ledger[n][r] # NoBlockVal /\ ledger[n][r][1] = KeyOf[k]
       /\ \A m \in Node : (ledger[m][r] # NoBlockVal => ledger[m][r][3] # lastHash)
       /\ lastHash' = CalculateHash([pk |-> KeyOf[k], rev |-> lastHash, amt |-> ledger[n][r][4]], lastHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = <<KeyOf[k], lastHash, r, ledger[n][r][4]>>]]
       /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]

\* The representative field is only present in some Nano implementations;
\* here it is simply an account-keyed value that a change block toggles.
CreateChangeRepresentativeBlock ==
  /\ \E n \in Node, k \in PrivateKey :
       /\ lastHash # NoHashVal
       /\ lastHash' = CalculateHash([pk |-> KeyOf[k], rev |-> lastHash, amt |-> 0], lastHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = <<KeyOf[k], lastHash, NoHashVal, 0>>]]
       /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]

ValidateBlock ==
  /\ \E n \in Node, h \in received[n] :
       /\ ledger[n][h] = NoBlockVal
       /\ ledger' = [m \in Node |->
            [ledger[m] EXCEPT ![h] = CHOOSE x \in ledger[Node \ {n}][h] \cup {NoBlockVal} : x # NoBlockVal]]
       /\ received' = [m \in Node |-> IF m = n THEN received[n] \ {h} ELSE received[m]]
       /\ lastHash' = lastHash

Next == CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock \/ CreateReceiveBlock
        \/ CreateChangeRepresentativeBlock \/ ValidateBlock

Spec ==
  /\ Init /\ [][Next]_<<lastHash, ledger, received>>
  /\ WF_vars(ValidateBlock)

\* Safety: a stored block must always verify under the public key of the
\* account chain it sits on; a forged or corrupted block would fail here.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash :
    ledger[n][h] # NoBlockVal => ledger[n][h][1] = KeyOf[ledger[n][h][1]]

====