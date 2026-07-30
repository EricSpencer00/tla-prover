---- MODULE Nano ----
EXTENDS Naturals

\* Nano cryptocurrency: a block-lattice blockchain model that emphasizes hash
\* functions and cryptographic signatures. A block-lattice stores one chain per
\* account, so action order is written into the data structure itself and the
\* state space grows super-exponentially. Hash calculation is abstracted into
\* an operator (CalculateHashFn) so the spec itself stays finite.

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance
CONSTANTS NoBlockVal, NoHash, NoBlock

Key == PrivateKey \cup PublicKey

\* Account chains are stored in a single record keyed by the hash of the last
\* block in each account's chain. Each block records:
\*   - account: the public key of the account it belongs to
\*   - prev: the hash of the previous block in that account's chain, or NoHash
\*   - kind: the block type (genesis, send, open, receive, change)
\*   - amount: the currency amount the block moves (zero for non-funding blocks)
\*   - signer: the private key that signed the block
\*   - recv: the hash of the send block this block receives, or NoHash
Block == [account: PublicKey, prev: Hash, kind: {"genesis", "send", "open", "receive", "change"}, amount: Nat, signer: PrivateKey, recv: Hash]

VARIABLES lastHash, ledger, received
vars == <<lastHash, ledger, received>>

\* NodeLedger is each node's local replicated copy of the distributed ledger.
NodeLedger == [n \in Node |-> [h \in Hash |-> NoBlock]]
NodeReceived == [n \in Node |-> {}]

BlockKinds == {"genesis", "send", "open", "receive", "change"}

\* NoHash represents "no previous block" (the start of every account chain).
\* NoBlock represents "no block stored here" (an empty slot or an unverified
\* block still in transit).
\* The no-hash sentinel is deliberately a real hash so that prev fields never
\* have to be type-checked as "hash or nothing".
NoHash == NoHashVal

RECURSIVE ChainBalance(_, _)
ChainBalance(a, h) ==
  IF h = NoHash THEN 0
  ELSE LET b == ledger[h] IN
       IF b.account = a THEN b.amount + ChainBalance(a, b.prev)
       ELSE ChainBalance(a, b.prev)

\* BalanceOf uses ChainBalance to walk the entire account chain in reverse.
BalanceOf(a) == ChainBalance(a, lastHash)

\* SumBalances asserts that the total currency across all account chains is
\* conserved; it is NOT the main safety invariant but is kept separate for
\* reference, since it requires unbounded recursion.
\* Unbounded recursion makes it unsuitable as a model-checking invariant.
RECURSIVE SumBalances(_)
SumBalances(S) ==
  IF S = {} THEN 0
  ELSE LET a == CHOOSE x \in S : TRUE IN BalanceOf(a) + SumBalances(S \ {a})

\* HashFn models the block hash as an abstract function of the block data and
\* the previous hash, which the .cfg substitutes with a bounded operator.
HashFn(block) == CalculateHash(block, block.prev)

TypeInvariant ==
  /\ lastHash \in {NoHash, Hash}
  /\ ledger \in [Hash -> Block \cup {NoBlock}]
  /\ received \in [Node -> SUBSET Hash]

\* Every stored block must pass signature verification against the account's
\* public key -- the only one thing the spec model-checks.
SafetyInvariant ==
  \A h \in Hash :
    ledger[h] # NoBlock =>
      /\ ledger[h].signer \in PrivateKey
      /\ [ledger[h].signer |-> ledger[h].account] \in [PrivateKey -> PublicKey]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [h \in Hash |-> NoBlock]
  /\ received = NodeReceived

CreateGenesis(n) ==
  /\ lastHash = NoHash
  /\ \E pk \in PrivateKey :
       LET block == [account |-> [pk |-> PublicKey][pk], prev |-> NoHash, kind |-> "genesis",
                     amount |-> GenesisBalance, signer |-> pk, recv |-> NoHash] IN
         /\ lastHash' = HashFn(block)
         /\ ledger' = [h \in Hash |-> IF h = HashFn(block) THEN block ELSE NoBlock]
         /\ received' = [m \in Node |-> IF m = n THEN {[node] <<- n, hash, HashFn(block)>>} ELSE received[m]]
  /\ UNCHANGED <<>>

CreateSend(n) ==
  /\ lastHash # NoHash
  /\ \E pk \in PrivateKey, amt \in Nat :
       /\ BalanceOf([pk |-> PublicKey][pk]) >= amt
       /\ amt > 0
       /\ LET block == [account |-> [pk |-> PublicKey][pk], prev |-> lastHash, kind |-> "send",
                         amount |-> amt, signer |-> pk, recv |-> NoHash] IN
            /\ lastHash' = HashFn(block)
            /\ ledger' = [h \in Hash |-> IF h = HashFn(block) THEN block ELSE ledger[h]]
            /\ received' = [m \in Node |-> IF m = n THEN received[m] \cup {[node |-> n, hash |-> HashFn(block)]} ELSE received[m]]
  /\ UNCHANGED <<>>

CreateOpen(n) ==
  /\ lastHash # NoHash
  /\ \E pk \in PrivateKey, sendH \in Hash :
       /\ ledger[sendH] # NoBlock
       /\ ledger[sendH].kind = "send"
       /\ ledger[sendH].account = [pk |-> PublicKey][pk]
       /\ ledger[sendH].recv = NoHash
       /\ ledger[pk] = NoBlock
       /\ LET block == [account |-> [pk |-> PublicKey][pk], prev |-> NoHash, kind |-> "open",
                         amount |-> ledger[sendH].amount, signer |-> pk, recv |-> sendH] IN
            /\ lastHash' = HashFn(block)
            /\ ledger' = [h \in Hash |-> IF h = HashFn(block) THEN block ELSE ledger[h]]
            /\ received' = [m \in Node |-> IF m = n THEN received[m] \cup {[node |-> n, hash |-> HashFn(block)]} ELSE received[m]]
  /\ UNCHANGED <<>>

CreateReceive(n) ==
  /\ lastHash # NoHash
  /\ \E pk \in PrivateKey, sendH \in Hash :
       /\ ledger[sendH] # NoBlock
       /\ ledger[sendH].kind = "send"
       /\ ledger[sendH].account = [pk |-> PublicKey][pk]
       /\ ledger[sendH].recv = NoHash
       /\ LET block == [account |-> [pk |-> PublicKey][pk], prev |-> lastHash, kind |-> "receive",
                         amount |-> ledger[sendH].amount, signer |-> pk, recv |-> sendH] IN
            /\ lastHash' = HashFn(block)
            /\ ledger' = [h \in Hash |-> IF h = HashFn(block) THEN block ELSE ledger[h]]
            /\ received' = [m \in Node |-> IF m = n THEN received[m] \cup {[node |-> n, hash |-> HashFn(block)]} ELSE received[m]]
  /\ UNCHANGED <<>>

CreateChange(n) ==
  /\ lastHash # NoHash
  /\ \E pk \in PrivateKey :
       /\ LET block == [account |-> [pk |-> PublicKey][pk], prev |-> lastHash, kind |-> "change",
                         amount |-> 0, signer |-> pk, recv |-> NoHash] IN
            /\ lastHash' = HashFn(block)
            /\ ledger' = [h \in Hash |-> IF h = HashFn(block) THEN block ELSE ledger[h]]
            /\ received' = [m \in Node |-> IF m = n THEN received[m] \cup {[node |-> n, hash |-> HashFn(block)]} ELSE received[m]]
  /\ UNCHANGED <<>>

ValidateBlock(n) ==
  /\ \E hash \in received[n] : TRUE
  /\ \E hash \in received[n] :
       /\ ledger[hash] = NoBlock
       /\ LET b == ledger[hash] IN
            /\ [b.signer |-> PublicKey] \in [PrivateKey -> PublicKey]
            /\ IF b.prev = NoHash THEN TRUE ELSE ledger[b.prev] # NoBlock
            /\ CASE b.kind = "genesis" -> TRUE
                [] b.kind = "send" ->
                    /\ b.amount > 0
                    /\ b.amount <= BalanceOf(b.account)
                [] b.kind = "open" ->
                    /\ ledger[b.recv] # NoBlock
                    /\ ledger[b.recv].kind = "send"
                    /\ ledger[b.recv].account = b.account
                [] b.kind = "receive" ->
                    /\ ledger[b.recv] # NoBlock
                    /\ ledger[b.recv].kind = "send"
                    /\ ledger[b.recv].account = b.account
                [] b.kind = "change" -> TRUE
       /\ ledger' = [ledger EXCEPT ![hash] = ledger[hash]]
       /\ received' = [received EXCEPT ![n] = received[n] \ {hash}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesis(n)
  \/ \E n \in Node : CreateSend(n)
  \/ \E n \in Node : CreateOpen(n)
  \/ \E n \in Node : CreateReceive(n)
  \/ \E n \in Node : CreateChange(n)
  \/ \E n \in Node : ValidateBlock(n)

Spec == Init /\ [][Next]_vars

====