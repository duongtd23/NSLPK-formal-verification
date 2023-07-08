## NSLPK formal verification

You can find in this repository:
- `nslpk.cafe`: The formal specification of the NSLPK protocol. The detailed explanation is given below.
- `invariants.cafe`: The invariant properties and lemmas. The descriptions of invariant properties are given below.
- `inputs`: Input scripts for IPSG to produce the proof scores.
- `nspk`: The formal specification of the NSPK protocol and a counterexample of its secrecy property. See README in that folder. This is mainly to show that we correctly specify NSLPK.
- other files: The proofs of invariants and lemmas.

---
### CafeOBJ Specification
Module `PRINCIPAL` specifies protocol participants. `priK(A)` and `pubK(A)` respectively denote the private key and public key of `A`. 

```
mod* PRINCIPAL {
  [Prin PubKey PriKey]
  op intru : -> Prin {constr}
  op priK : Prin -> PriKey {constr}
  op pubK : Prin -> PubKey {constr}
  vars A B : Prin 
  eq (priK(A) = priK(B)) = (A = B) .
  eq (pubK(A) = pubK(B)) = (A = B) .
}
```

Module `NONCE` specifies nonces:
```
mod! NONCE {
  [Nonce]
}
```

We introduce module `DATA` with sorts `Data` and `DataL` representing generic data types, i.e., the supersorts of all sorts introduced so far. `||` and `\in` are concatenation operator and membership operator, respectively.

```
mod! DATA {
  pr(PRINCIPAL + NONCE)
  [Data < DataL]
  [Prin PubKey PriKey Nonce < Data]
  op _||_ : DataL DataL -> DataL {assoc r-assoc constr}

  op _\in_ : DataL DataL -> Bool
```

The two operators are defined by some equations, for example:

```
  ceq (P = D1)   = false if (D1 :is PriKey) or 
                            (D1 :is PubKey) or 
                            (D1 :is Nonce) .
```
specifies that any private key, public key, and nonce cannot equal a principal.

We define asymmetric encryption and decryption in module `ENCRYPTION`:

```
mod! ENCRYPTION {
  pr(DATA)
  
--          Key   Plaintext     Ciphertext
  op aenc : Data  DataL      -> Data {constr}
--          Key   Ciphertext    Plaintext
  op adec : Data  Data       -> DataL
```

We specify the cancelation property of asymmetric encryption and decryption:
```
  eq adec(pubK(A), aenc(priK(A),DL)) = DL .
  eq adec(priK(A), aenc(pubK(A),DL)) = DL .
```

We consider only encryption with public/private keys:
```
  ceq (adec(KE, D) = DL2) = false 
    if (KE :is Prin) or (KE :is Nonce) .
```

We specify that ciphertext of encryption cannot equal a principal/private key/public key/nonce:
```
  ceq (aenc(KE,DL) = D) = false if (D :is Prin) or 
                                   (D :is PriKey) or 
                                   (D :is PubKey) or 
                                   (D :is Nonce) .
```

Module `MESSAGE` specifies messages exchanged in the protocol:
```
mod! MESSAGE {
  pr(ENCRYPTION)
  [Msg]
  op msg1 : Prin Prin Prin DataL -> Msg {constr}
  op msg2 : Prin Prin Prin DataL -> Msg {constr}
  op msg3 : Prin Prin Prin DataL -> Msg {constr}
```

`init` represents all initial states. `send1`, `send2`, and `send3` specify a principal sends the first, second, and third messages, respectively. Three observer `nw`, `unonce`, and `knl` observing the network, the set of used nonces, the knowledge of the intruder.

```
mod NSLPK {
  pr(NETWORK)
  pr(SET(D <= TRIV2DATA)*{sort Set -> NonceSet})
  [Sys]
-- initial states
  op init : -> Sys {constr}
  op send1 : Sys Prin Prin Nonce -> Sys {constr}
  op send2 : Sys Prin Prin Prin Data Nonce Nonce -> Sys {constr}
  op send3 : Sys Prin Prin Prin Data Nonce Nonce -> Sys {constr}

  op nw : Sys -> Network
  op unonce : Sys -> NonceSet
  op knl : Sys -> DataL
```

The initial state is defined as follow:
```
  eq nw(init) = void .
  eq unonce(init) = empty .
  eq knl(init) = (priK(intru) || pubK(intru)) .
```

Transition `send1` specifies principal `A` send the first message to principal `B`. Note that the sent ciphertext `aenc(pubK(B), A || N)` is also added to the intruder knowledge, meaning that the intruder gleans the ciphertext.

```
  op c-send1 : Sys Nonce -> Bool
  eq c-send1(S,N) = not(N \in unonce(S)) .
  ceq nw(send1(S,A,B,N)) = 
      (msg1(A,A,B, aenc(pubK(B), A || N)) , nw(S)) 
    if c-send1(S,N) .
  ceq unonce(send1(S,A,B,N)) = (N unonce(S)) 
    if c-send1(S,N) .
  ceq knl(send1(S,A,B,N)) = 
      (aenc(pubK(B), A || N) || knl(S)) 
    if c-send1(S,N) .
  ceq send1(S,A,B,N) = S 
    if not c-send1(S,N) .
```

Transitions `send2` and `send3` are defined similarly.

We turn to specify the intruder.
The intruder can randomly select a nonce `N` (which must be unused before), and added to its knowledge:
```
  op gNonce : Sys Nonce -> Sys {constr}
  op c-gNonce : Sys Nonce -> Bool
  eq c-gNonce(S,N) = not(N \in unonce(S)) .
  eq nw(gNonce(S,N)) = nw(S) .
  ceq unonce(gNonce(S,N)) = (N unonce(S))
    if c-gNonce(S,N) .
  ceq knl(gNonce(S,N)) = (N || knl(S))
    if c-gNonce(S,N) .
  ceq gNonce(S,N) = S 
    if not c-gNonce(S,N) .
```

Any values of basic data types are known by the intruder:
```
  op gBasic : Sys Prin PubKey -> Sys {constr}
  eq nw(gBasic(S,A,PK)) = nw(S) .
  eq unonce(gBasic(S,A,PK)) = unonce(S) .
  eq knl(gBasic(S,A,PK)) = (A || PK || knl(S)) .
``` 

Given two pieces of data `D1` and `DL2`, which are available to the intruder, the intruder can encrypt `DL2` by usung `D1` as the key and learn the obtained ciphertext:
```
  op g2 : Sys Data DataL -> Sys {constr}
  op c-g2 : Sys Data DataL -> Bool
  eq c-g2(S,D1,DL2) = (D1 \in knl(S) and DL2 \in knl(S)) .
  eq nw(g2(S,D1,DL2)) = nw(S) .
  eq unonce(g2(S,D1,DL2)) = unonce(S) .
  ceq knl(g2(S,D1,DL2)) = 
      (aenc(D1,DL2) || knl(S)) 
    if c-g2(S,D1,DL2) .
  ceq g2(S,D1,DL2) = S if not c-g2(S,D1,DL2) .
```

With this protocol, the intruder can decrypt a ciphertext only if they know the correct key:
```
  op g21 : Sys Prin DataL -> Sys {constr}
  op c-g21 : Sys Prin DataL -> Bool
  eq c-g21(S,A,DL) = 
    (priK(A) \in knl(S) and aenc(pubK(A),DL) \in knl(S)) .
  eq nw(g21(S,A,DL)) = nw(S) .
  eq unonce(g21(S,A,DL)) = unonce(S) .
  ceq knl(g21(S,A,DL)) = (DL || knl(S))
    if c-g21(S,A,DL) .
  ceq g21(S,A,DL) = S if not c-g21(S,A,DL) .
```

If a piece of data `D1` is available to the intruder, the intruder can use it as the ciphertext, pretend `A`, send it to `B`:
```
  op fkmsg1 : Sys Prin Prin Data -> Sys {constr}
  op c-fkmsg1 : Sys Prin Prin Data -> Bool
  eq c-fkmsg1(S,A,B,D1) = 
    (D1 \in knl(S)) .
  ceq nw(fkmsg1(S,A,B,D1)) = 
      (msg1(intru,A,B, D1) , nw(S))
    if c-fkmsg1(S,A,B,D1) .
  eq unonce(fkmsg1(S,A,B,D1)) = unonce(S) .
  eq knl(fkmsg1(S,A,B,D1)) = knl(S) .
  ceq fkmsg1(S,A,B,D1) = S 
    if not c-fkmsg1(S,A,B,D1) .
```

The two other transitions `fkmsg2` and `fkmsg3`, which specify the intruder sends a faking 2nd message and a faking 3rd message, are defined similarly.

---
### Formal verification
In the file `invariants.cafe`, you can finds:
The two predicates `keySe` and `keySe2` specifying the secrecy propery of a nonce from the initiator point of view and the responder point of view, respectively:

```
  op keySe : Sys Prin Prin Prin Nonce Nonce Data -> Bool
  eq keySe(S,B2,A,B,N,N2,D) = 
  (not(A = intru or B = intru) and
    msg1(A,A,B, aenc(pubK(B), A || N)) \in nw(S) and
    msg2(B2,B,A, D) \in nw(S) and 
    adec(priK(A), D) = N || N2 || B)
   implies not(N \in knl(S)) .

  op keySe2 : Sys Prin Prin Prin Nonce Nonce Data Data -> Bool
  eq keySe2(S,A2,A,B,N,N2,D,D2) = 
  (not(A = intru or B = intru) and
    msg1(A2,A,B, D) \in nw(S) and 
    adec(priK(B), D) = A || N and 
    msg2(B,B,A, aenc(pubK(A), N || N2 || B)) \in nw(S) and 
    msg3(A2,A,B, D2) \in nw(S) and 
    adec(priK(B), D2) = N2)
   implies not(N2 \in knl(S)) .
```
`keySe` states that if initiator `A` has sent a `msg1` message to `B` and received a `msg2` message apparently from `B` with a valid ciphertext, then the nonce `N` that `A` sent to `B` is secure, i.e., `N` is not in the intruder knowledge.
`keySe2` states that if `B` has received a valid `msg1` message apparently from `A`, `B` has replied to `A` with a `msg2` message, and received another valid `msg3` message apparently from `A`, then the nonce `N2` that `B` sent to `A` is not in the intruder knowledge.

To prove `keySe`, we use a stronger predicate:
```
  op inv1 : Sys Prin Prin Nonce -> Bool
  eq inv1(S,A,B,N) = 
   (not(A = intru or B = intru) and
    msg1(A,A,B, aenc(pubK(B), A || N)) \in nw(S))
   implies not(N \in knl(S)) .
```

And the proof is simply as follows (see file `keySe.cafe`):
```
  red inv1(s,a,b,n) implies keySe(s,b2,a,b,n,n2,d) .
```

`inv1` is prove by induction with the employment of IPSG, where some auxilary lemmas are needed. Similarly, to prove `keySe2`, we use a stronger predicate `inv0`.

```
  op inv0 : Sys Prin Prin Nonce Nonce -> Bool
  eq inv0(S,A,B,N,N2) = 
  (not(A = intru or B = intru) and
    msg2(B,B,A, aenc(pubK(A), N || N2 || B)) \in nw(S))
   implies not(N2 \in knl(S)) .
```

The predicate `auth` specifies the authentication property from the initiator point of view:
```
  op auth : Sys Prin Prin Prin Nonce Nonce Data -> Bool
  eq auth(S,B2,A,B,N,N2,D) = 
  (not(A = intru or B = intru) and
    msg1(A,A,B, aenc(pubK(B), A || N)) \in nw(S) and
    msg2(B2,B,A, D) \in nw(S) and 
    adec(priK(A), D) = N || N2 || B)
   implies msg2(B,B,A, D) \in nw(S) .
```
Precisely, `auth` states that if initiator `A` has sent a `msg1` message to `B` and received a `msg2` message apparently from `B` with a valid ciphertext, then the message was indeed sent by `B`. `auth` is proved by induction.

From `auth` and `keySe2`, we can derive the secrecy property of the nonce created by the responder (nonce `N2`) from the initiator point of view. That is, the following property:

```
  op keySe3 : Sys Prin Prin Prin Nonce Nonce Data -> Bool
  eq keySe3(S,B2,A,B,N,N2,D) = 
  (not(A = intru or B = intru) and
    msg1(A,A,B, aenc(pubK(B), A || N)) \in nw(S) and
    msg2(B2,B,A, D) \in nw(S) and 
    adec(priK(A), D) = N || N2 || B and
    msg3(A,A,B, aenc(pubK(B), N2)) \in nw(S))
   implies not(N2 \in knl(S)) .
```
is proved by `auth` and `keySe2`.

The predicates `auth2` and `auth3` specify the authentication property from the responder point of view:
```
  op auth2 : Sys Prin Prin Prin Nonce Nonce Data -> Bool
  eq auth2(S,A2,A,B,N,N2,D2) = 
  (not(A = intru or B = intru) and
    msg2(B,B,A, aenc(pubK(A), N || N2 || B)) \in nw(S) and 
    msg3(A2,A,B, D2) \in nw(S) and 
    adec(priK(B), D2) = N2)
   implies msg3(A,A,B, D2) \in nw(S) .

  op auth3 : Sys Prin Prin Prin Nonce Nonce Data -> Bool
  eq auth3(S,A2,A,B,N,N2,D2) = 
  (not(A = intru or B = intru) and
    msg2(B,B,A, aenc(pubK(A), N || N2 || B)) \in nw(S) and 
    msg3(A2,A,B, D2) \in nw(S) and 
    adec(priK(B), D2) = N2)
   implies msg1(A,A,B, D2) \in nw(S) .
```
Precisely, the two predicates states that if `B` has sent a `msg2` message to `A` and received back `msg3` message apparently sent from `A` with a valid ciphertext, then `A` indeed sent that `msg3` message to `B` and `A` also sent a `msg1` message to `B`.

Similarly, from `auth3` and `keySe`, we can derive the secrecy property of the nonce created by the initiator (nonce `N`) from the responder point of view. 