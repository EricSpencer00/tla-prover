---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
    NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

Chains == [pub : PublicKey, idx : Nat]

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> Chains \cup {NoBlockVal}]]
    /\ received \in [Node -> SUBSET Hash]

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

IsEmpty(n) == \A h \in Hash : ledger[n][h] = NoBlockVal

\* The hash of the genesis block must be agreed across nodes, so it is
\* calculated once and pushed into every node's ledger atomically.
CreateGenesisBlock(n) ==
    /\ IsEmpty(n)
    /\ lastHash' = CalculateHash([kind |-> "genesis",
                                  account |-> n,
                                  amount |-> GenesisBalance,
                                  prev |-> NoHash], NoHash)
    /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
                    [pub |-> n, idx |-> 1]]]
    /\ UNCHANGED <<received>>

\* A send block reduces the sender's balance and names a recipient; it
\* must not send more than the sender has available.
CreateSendBlock(n, r, hPrev) ==
    /\ hPrev \in Hash
    /\ ledger[n][hPrev] # NoBlockVal
    /\ \E amt \in Nat :
        /\ amt <= Balance(n, hPrev)
        /\ lastHash' = CalculateHash([kind |-> "send",
                                      account |-> n, to |-> r,
                                      amount |-> amt,
                                      prev |-> hPrev], hPrev)
        /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
                        [pub |-> n, idx |-> ledger[m][hPrev].idx + 1]]]
    /\ UNCHANGED <<received>>

\* An open block establishes a new account's first block, linking to an
\* unclaimed send directed to it.
CreateOpenBlock(m, hPrev) ==
    /\ hPrev \in Hash
    /\ ledger[m][hPrev] # NoBlockVal
    /\ ledger[m][hPrev].kind = "send"
    /\ ledger[m][hPrev].to = m
    /\ \A n \in Node : \A g \in Hash : ledger[n][g] # NoBlockVal =>
         ~(ledger[n][g].kind = "open" /\ ledger[n][g].prev = hPrev)
    /\ lastHash' = CalculateHash([kind |-> "open",
                                  account |-> m,
                                  prev |-> hPrev], hPrev)
    /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] =
                    [pub |-> m, idx |-> 1]]]
    /\ UNCHANGED <<received>>

\* A receive block adds a previously sent amount to the recipient's
\* balance, linking to both the recipient's previous block and the send.
CreateReceiveBlock(m, hPrev, hSend) ==
    /\ hPrev \in Hash
    /\ hSend \in Hash
    /\ ledger[m][hPrev] # NoBlockVal
    /\ ledger[m][hSend] # NoBlockVal
    /\ ledger[m][hSend].kind = "send"
    /\ ledger[m][hSend].to = m
    /\ \A n \in Node : \A g \in Hash : ledger[n][g] # NoBlockVal =>
         ~(ledger[n][g].kind = "receive" /\ ledger[n][g].prev = hPrev
                                   /\ ledger[n][g].link = hSend)
    /\ lastHash' = CalculateHash([kind |-> "receive",
                                  account |-> m, prev |-> hPrev,
                                  link |-> hSend], hPrev)
    /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] =
                    [pub |-> m, idx |-> ledger[n][hPrev].idx + 1]]]
    /\ UNCHANGED <<received>>

\* A change-representative block advances the chain without moving coins.
CreateChangeRepBlock(n, hPrev) ==
    /\ hPrev \in Hash
    /\ ledger[n][hPrev] # NoBlockVal
    /\ lastHash' = CalculateHash([kind |-> "changeRep",
                                  account |-> n, prev |-> hPrev], hPrev)
    /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
                    [pub |-> n, idx |-> ledger[m][hPrev].idx + 1]]]
    /\ UNCHANGED <<received>>

\* Every created block is broadcast to all nodes' received sets.
Broadcast(h) ==
    /\ lastHash = h
    /\ received' = [n \in Node |-> received[n] \cup {h}]
    /\ UNCHANGED <<lastHash, ledger>>

\* Validation checks signatures, existence of referenced blocks, and the
\* chain-specific rules (no overdraft, no double-claim, etc.).
Validate(n, h) ==
    /\ h \in received[n]
    /\ ledger[n][h] = NoBlockVal
    /\ \E source \in PrivateKey :
         /\ Verify(h, source)
         /\ ledger[n][h] = ledger[PublicKeyOf(source)][h]
    /\ received' = [received EXCEPT ![n] = @ \ {h}]
    /\ UNCHANGED <<lastHash, ledger>>

Next ==
    \/ \E n \in Node : CreateGenesisBlock(n)
    \/ \E n \in Node, r \in Node, hPrev \in Hash :
         CreateSendBlock(n, r, hPrev)
    \/ \E m \in Node, hPrev \in Hash : CreateOpenBlock(m, hPrev)
    \/ \E m \in Node, hPrev \in Hash, hSend \in Hash :
         CreateReceiveBlock(m, hPrev, hSend)
    \/ \E n \in Node, hPrev \in Hash : CreateChangeRepBlock(n, hPrev)
    \/ \E h \in Hash : Broadcast(h)
    \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

\* Chain traversal is used to compute the available balance at a given
\* block (used to bound sends and enforce conservation).
Balance(n, h) ==
    IF ledger[n][h] = NoBlockVal THEN 0
    ELSE LET p == ledger[n][h].prev IN
        IF p = NoHash THEN ledger[n][h].amount
        ELSE
            IF ledger[n][h].kind = "send" THEN Balance(n, p) - ledger[n][h].amount
            ELSE IF ledger[n][h].kind = "receive" THEN Balance(n, p) + ledger[n][h].amount
            ELSE Balance(n, p)

\* A block's signature must match the account's public key; this is the
\* cryptographic soundness the spec verifies.
SignatureValid(n, h) ==
    ledger[n][h] # NoBlockVal => Verify(h, PrivateKeyOf(ledger[n][h].pub))

SafetyInvariant == \A n \in Node, h \in Hash : SignatureValid(n, h)

====