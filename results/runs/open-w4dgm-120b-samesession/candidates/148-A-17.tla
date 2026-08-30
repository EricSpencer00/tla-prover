---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

\* Original Nano protocol: a block-lattice blockchain where each account has its own
\* chain.  Actions create blocks of various types and broadcast them to every node's
\* received-set; per-node ledger copies accept a block only after validating its
\* signature and its predecessor links.  The safety invariant is the signature check.
CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Block types: genesis (initial coin placement), send (outbound transfer), open (first
\* block of a newly addressed account), receive (inbound transfer), change-rep.
BlockType == {"genesis", "send", "open", "receive", "change-rep"}

Assignee(h) == CHOOSE n \in Node : PrivateKey[n] = h

SumOver(f, S) ==
  LET g[T \in SUBSET S] ==
        IF T = {} THEN 0
        ELSE LET x == CHOOSE y \in T : TRUE IN f[x] + g[T \ {x}]
  IN g[S]

RECURSIVE ChainBalance(_)
ChainBalance(chain) ==
  IF chain = <<>> THEN 0
  ELSE LET h == Head(chain) IN
       IF h = NoHash THEN 0
       ELSE LET c == Instances[h] IN
            IF c.type = "send" THEN - c.amount + ChainBalance(Tail(chain))
            ELSE IF c.type = "receive" THEN c.amount + ChainBalance(Tail(chain))
            ELSE ChainBalance(Tail(chain))

Balance == ChainBalance(Chain)

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> (PublicKey \X BlockType \X (0 .. GenesisBalance \X (0 .. GenesisBalance)?) \X (PublicKey \cup {NoBlock}) \X Hash \cup {NoHash}) \cup {NoBlock}]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(n) ==
  /\ lastHash = NoHash
  /\ lastHash' = CalculateHash(<<PublicKey[n], "genesis", GenesisBalance, NoBlock, NoHash>>)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = <<PublicKey[n], "genesis", GenesisBalance, NoBlock, NoHash>>]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateSendBlock(n, amt, dst) ==
  /\ lastHash # NoHash
  /\ ChainBalance(ChainFor(Assignee(lastHash))) >= amt
  /\ lastHash' = CalculateHash(<<PublicKey[n], "send", amt, dst, lastHash>>)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = <<PublicKey[n], "send", amt, dst, lastHash>>]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateOpenBlock(n, src) ==
  /\ lastHash # NoHash
  /\ Instances[src].type = "send"
  /\ Instances[src].dst = PublicKey[n]
  /\ ~ \E h \in Range(ChainFor(PublicKey[n])) : Instances[h].type \in {"open", "receive"} /\ Instances[h].prev = src
  /\ lastHash' = CalculateHash(<<PublicKey[n], "open", 0, NoBlock, src>>)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = <<PublicKey[n], "open", 0, NoBlock, src>>]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateReceiveBlock(n, src) ==
  /\ lastHash # NoHash
  /\ Instances[src].type = "send"
  /\ Instances[src].dst = PublicKey[n]
  /\ ~ \E h \in Range(ChainFor(PublicKey[n])) : Instances[h].type = "receive" /\ Instances[h].prev = src
  /\ lastHash' = CalculateHash(<<PublicKey[n], "receive", Instances[src].amount, NoBlock, src>>)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = <<PublicKey[n], "receive", Instances[src].amount, NoBlock, src>>]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateChangeRepBlock(n) ==
  /\ lastHash # NoHash
  /\ lastHash' = CalculateHash(<<PublicKey[n], "change-rep", 0, NoBlock, lastHash>>)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = <<PublicKey[n], "change-rep", 0, NoBlock, lastHash>>]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

\* A node validates before accepting a block into its own copy of the ledger: the
\* signature must match the account, the previous hash must be present, and the
\* block must pass its type-specific checks (no overdraft, no duplicate receipt).
Validate(n, h) ==
  /\ h \in received[n]
  /\ Instances[h].type \in BlockType
  /\ Instances[h].key = PublicKey[n]
  /\ (IF Instances[h].type \in {"send", "open", "receive", "change-rep"} THEN TRUE ELSE FALSE)
  /\ IF Instances[h].prev = NoHash THEN TRUE ELSE ledger[n][Instances[h].prev] # NoBlock
  /\ IF Instances[h].type = "send" THEN Instances[h].dst \in PublicKey /\ Instances[h].amount <= Balance ELSE TRUE
  /\ IF Instances[h].type = "open" THEN Instances[h].dst = PublicKey[n] ELSE TRUE
  /\ IF Instances[h].type = "receive" THEN Instances[h].dst = PublicKey[n] ELSE TRUE
  /\ ledger' = [ledger EXCEPT ![n][h] = Instances[h]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n)
  \/ \E n \in Node, amt \in 1 .. GenesisBalance, dst \in PublicKey : CreateSendBlock(n, amt, dst)
  \/ \E n \in Node, src \in Hash : CreateOpenBlock(n, src)
  \/ \E n \in Node, src \in Hash : CreateReceiveBlock(n, src)
  \/ \E n \in Node : CreateChangeRepBlock(n)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

\* No forging: the block's recorded public key must match the key derived from the
\* node that allegedly authored it, for every block recorded in every node's ledger.
SafetyInvariant == \A n \in Node : \A h \in Range(ledger[n]) : Instances[h].key = PublicKey[Assignee(h)]

BalanceWithinGenesis == Balance <= GenesisBalance

====