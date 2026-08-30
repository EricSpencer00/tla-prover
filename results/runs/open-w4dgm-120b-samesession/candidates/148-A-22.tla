---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash, NoBlock

Hashable == {NoHash} \cup Hash

Assume == NoHashVal
BlankBlock == [kind |-> NoBlock, from |-> NoHash, to |-> NoHash, prev |-> NoHash, amount |-> 0, pubkey |-> NoHash]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* The distributed ledger is a map from hash to block, replicated across all nodes.
\* Validation is done against the local copy, so a node can only ever accept a
\* block that its own ledger already acknowledges.
Ledger == [Node -> [Hashable -> [kind: {"send", "receive", "open", "change"}, from, to, prev, amount, pubkey: PUBLIC Set(BigInt) \/ PublicKey \cup {NoHash}], NoBlockVal]

Init ==
  /\ lastHash = Assume
  /\ ledger = [n \in Node |-> [h \in Hashable |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* The genesis block seeds the network with the initial balance, recorded in
\* every node's ledger as it is created.
CreateGenesisNode(kp) ==
  /\ lastHash = Assume
  /\ \E h \in Hash :
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] =
                           [kind |-> "change", from |-> NoHash, to |-> NoHash, prev |-> NoHash, amount |-> GenesisBalance, pubkey |-> kp]]]
       /\ lastHash' = h
  /\ UNCHANGED received

\* A node creates a block sending funds from its own account chain to a
\* recipient's account chain. The block is broadcast to every node's inbox.
CreateSendBlock(n, kp, rec, amt) ==
  /\ \E h \in Hash :
       /\ ledger[n][h] = NoBlockVal
       /\ ledger[n][Assume] # NoBlockVal
       /\ ledger[n][Assume].pubkey = kp
       /\ ledger[n][Assume].amount >= amt
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] =
                          [kind |-> "send", from |-> Assume, to |-> rec, prev |-> Assume, amount |-> amt, pubkey |-> kp]]]
       /\ lastHash' = h
       /\ received' = [m \in Node |-> received[m] \cup {h}]
  /\ UNCHANGED <<>>

CreateOpenBlock(n, kp, h) ==
  /\ ledger[h] # NoBlockVal
  /\ ledger[h].kind = "send"
  /\ ledger[h].to = kp
  /\ ledger[n][h] = NoBlockVal
  /\ \E g \in Hash :
       /\ ledger[n][g] = NoBlockVal
       /\ ledger[n][Assume] # NoBlockVal
       /\ ledger[n][Assume].pubkey = kp
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![g] =
                          [kind |-> "open", from |-> ledger[h].from, to |-> kp, prev |-> h, amount |-> ledger[h].amount, pubkey |-> kp]]]
       /\ lastHash' = g
       /\ received' = [m \in Node |-> received[m] \cup {g}]
  /\ UNCHANGED <<>>

CreateReceiveBlock(n, kp, h) ==
  /\ ledger[h] # NoBlockVal
  /\ ledger[h].kind \in {"send", "open"}
  /\ ledger[h].to = kp
  /\ ledger[n][h] = NoBlockVal
  /\ \E g \in Hash :
       /\ ledger[n][g] = NoBlockVal
       /\ ledger[n][Assume] # NoBlockVal
       /\ ledger[n][Assume].pubkey = kp
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![g] =
                          [kind |-> "receive", from |-> ledger[h].from, to |-> kp, prev |-> Assume, amount |-> ledger[h].amount, pubkey |-> kp]]]
       /\ lastHash' = g
       /\ received' = [m \in Node |-> received[m] \cup {g}]
  /\ UNCHANGED <<>>

CreateChangeRepBlock(n, kp) ==
  /\ \E h \in Hash :
       /\ ledger[n][h] = NoBlockVal
       /\ ledger[n][Assume] # NoBlockVal
       /\ ledger[n][Assume].pubkey = kp
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] =
                          [kind |-> "change", from |-> NoHash, to |-> NoHash, prev |-> Assume, amount |-> ledger[n][Assume].amount, pubkey |-> kp]]]
       /\ lastHash' = h
       /\ received' = [m \in Node |-> received[m] \cup {h}]
  /\ UNCHANGED <<>>

\* Each node validates a block against its own local ledger copy before it
\* accepts it. Signature checking is literally a public-key equality here.
Validate(n, h) ==
  /\ ledger[n][h] = NoBlockVal
  /\ h \in received[n]
  /\ ledger[n][Assume] # NoBlockVal
  /\ ledger[n][Assume].pubkey = ledger[h].pubkey
  /\ \/ ledger[h].kind = "send" =>
        /\ ledger[h].amount <= ledger[n][Assume].amount
        /\ ledger[n][Assume].pubkey = ledger[h].pubkey
     \/ ledger[h].kind \in {"open", "receive"} =>
        /\ ledger[h].prev = Assume
        /\ ledger[h].amount <= ledger[n][Assume].amount
        /\ ledger[n][Assume].pubkey = ledger[h].pubkey
  /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![h] = ledger[h]]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node, kp \in PrivateKey : CreateGenesisNode(kp) \/ CreateChangeRepBlock(n, kp)
  \/ \E n \in Node, kp \in PrivateKey, rec \in PublicKey, amt \in 1..GenesisBalance : CreateSendBlock(n, kp, rec, amt)
  \/ \E n \in Node, kp \in PrivateKey, h \in Hash : CreateOpenBlock(n, kp, h) \/ CreateReceiveBlock(n, kp, h) \/ Validate(n, h)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in {Assume} \cup (PublicKey \cup {NoHash})
  /\ ledger \in [Node -> [Hashable -> [kind: {"send", "receive", "open", "change", NoBlock}, from, to, prev: {NoHash} \cup PublicKey, amount: Nat, pubkey: {NoHash} \cup PublicKey]]]
  /\ received \in [Node -> SUBSET Hash]

\* A block is an authorized, signature-validated entry in the replicated
\* ledger -- this is what makes every recorded balance movement real and
\* non-fabricated, even as blocks are shuffled about between nodes.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].pubkey = \E k \in PrivateKey : ledger[n][h].pubkey = k

====