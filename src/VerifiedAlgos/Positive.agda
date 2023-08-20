{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

{-
Based on Software Foundations Vol 3 : Verified Functional Algoriths
by Andrew W. Appel

Chapter 12  Number Representations and Efficient Lookup Tables (Trie)
https://softwarefoundations.cis.upenn.edu/current/vfa-current/Maps.html

Coq standard library: https://github.com/coq/coq/blob/master/theories/PArith/BinPosDef.v
-}

module VerifiedAlgos.Positive where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.List using (List; _∷_; []; [_]; _++_)

data Pos : Set where
  P1n : Pos → Pos -- 1 + 2*n
  P0n : Pos → Pos -- 0 + 2*n
  P1  : Pos       -- 1

pos2nat : Pos → ℕ
pos2nat (P1n p) = 1 + 2 * pos2nat p
pos2nat (P0n p) = 0 + 2 * pos2nat p
pos2nat P1      = 1

ten = P0n (P1n (P0n P1)) -- 0 + 2(1 + 2(0 + 2*1)) = 2*(1 + 4) = 10

testPos2nat : (pos2nat ten) ≡ 10
testPos2nat = refl

showPos : Pos → List ℕ
showPos (P1n q) = (showPos q) ++ [ 1 ]
showPos (P0n q) = (showPos q) ++ [ 0 ]
showPos P1      = [ 1 ]

testShowPos : showPos ten ≡ 1 ∷ 0 ∷ 1 ∷ 0 ∷ [] 
testShowPos = refl

sucPos : Pos → Pos
sucPos (P1n p) = P0n (sucPos p) -- 1+2p +1 = 2(p+1)
sucPos (P0n p) = P1n p          -- 2p + 1 = 1+2p
sucPos P1      = P0n P1         -- 1 + 1 = 2*1

posSucCorrect : ∀ p → pos2nat (sucPos p) ≡ suc (pos2nat p)
posSucCorrect P1      = refl
posSucCorrect (P0n p) = refl
posSucCorrect (P1n p)
 rewrite (posSucCorrect p)
 | +-identityʳ (pos2nat p)
 | +-suc (pos2nat p) (pos2nat p) = refl

addPosLoop : Bool → Pos → Pos → Pos
addPosLoop false (P1n p) (P1n q) = P1n (addPosLoop true p q)  -- 1+2p + 1+2q = 2*(p + q+1) = 1+2(p + q) (+1)
addPosLoop false (P1n p) (P0n q) = P1n (addPosLoop false p q) -- 1+2p + 2q = 1+2(p + q)
addPosLoop false (P0n p) (P1n q) = P1n (addPosLoop false p q) -- 2p + 1+2q = 1+2(p + q)
addPosLoop false (P0n p) (P0n q) = P0n (addPosLoop false p q) -- 2p + 2q = 2(p + q)
addPosLoop false (P1n p) P1      = P0n (sucPos p)             -- 1+2p + 1 = 2*(p+1)
addPosLoop false P1      (P1n q) = P0n (sucPos q)             -- 1 + 1+2q = 0+2(q+1)
addPosLoop false (P0n p) P1      = P1n p                      -- 2p + 1 = 1+2p
addPosLoop false P1      (P0n q) = P1n q                      -- 1 + 2*q
addPosLoop false P1      P1      = P0n P1                     -- 1 + 1 = 2*1
addPosLoop true  (P1n p) (P1n q) = sucPos (P1n (addPosLoop true p q)) -- 1+2p + 1+2q (+1) = 1 + 1+2*(p + q) (+1)
addPosLoop true  (P1n p) (P0n q) = P1n (addPosLoop true p q)  -- 1+2p + 2q (+1) = 1+2(p + q) (+1)
addPosLoop true  (P0n p) (P1n q) = P1n (addPosLoop true p q)  -- 2p + 1+2q (+1) = 1+2(p + q) (+1)
addPosLoop true  (P0n p) (P0n q) = P1n (addPosLoop false p q) -- 2p + 2q (+1) = 1+2(p + q)
addPosLoop true  (P1n p) P1      = P1n (sucPos p)  -- 1+2p + 1 (+1) = 1+2(p+1)
addPosLoop true  P1      (P1n q) = P1n (sucPos q)  -- 1 + 1+2q (+1) = 1+2(q+1)
addPosLoop true  (P0n p) P1      = P0n (sucPos p)  -- 2p + 1 (+1) = 2(p+1)
addPosLoop true  P1      (P0n q) = P0n (sucPos q)  -- 1 + 2q + (+1) = 2(q+1)
addPosLoop true  P1      P1      = P1n P1          -- 1 + 1 (+1) = 1+2*1

_+P_ : Pos → Pos → Pos
x +P y = addPosLoop false x y

{-
addPosLoopCorrect : ∀ (c : Bool) (p q : Pos) → pos2nat (addPosLoop c p q) ≡
  (if c then 1 else 0) + (pos2nat p) + (pos2nat q)
addPosLoopCorrect = ?

addPosCorrect : ∀ (p q : Pos) → pos2nat (addPos p q) ≡ (pos2nat p) + (pos2nat q)
addPosCorrect = ?
-}

-- p -> 2p-1
p2x-1 : Pos → Pos
p2x-1 (P1n p) = P1n (P0n p)   -- 2*(1+2p) - 1 = 1+2(2p)
p2x-1 (P0n p) = P1n (p2x-1 p) -- 2*(2p) - 1 = 1+2*(2*p - 1)
p2x-1 P1      = P1

_*2P : Pos → Pos
p *2P = P0n p

-- n*2≡n+n : ∀ (n : Pos) → n *2P ≡ n +P n
-- n*2≡n+n (P1n n) = {!   !}
-- n*2≡n+n (P0n n) = {!   !}
-- n*2≡n+n P1 = {!   !}

-- predPos : Pos → Pos
-- predPos p = {!   !}

data Comparison : Set where
  Eq : Comparison
  Lt : Comparison
  Gt : Comparison

_≡ᵇ_ : Comparison → Comparison → Bool -- TODO Dec
Eq ≡ᵇ Eq = true
Eq ≡ᵇ Lt = false
Eq ≡ᵇ Gt = false
Lt ≡ᵇ Eq = false
Lt ≡ᵇ Lt = true
Lt ≡ᵇ Gt = false
Gt ≡ᵇ Eq = false
Gt ≡ᵇ Lt = false
Gt ≡ᵇ Gt = true

_≡Posᵇ_ : Pos → Pos → Bool
P1    ≡Posᵇ P1    = true
P1n a ≡Posᵇ P0n b = false
P1n a ≡Posᵇ P1    = false
P0n a ≡Posᵇ P1n b = false
P0n a ≡Posᵇ P1    = false
P1    ≡Posᵇ P1n b = false
P1    ≡Posᵇ P0n b = false
P1n a ≡Posᵇ P1n b = a ≡Posᵇ b
P0n a ≡Posᵇ P0n b = a ≡Posᵇ b

{-
comparePos : Pos → Pos → Comparison
comparePos (P1n p) (P1n q) = comparePos p q
comparePos (P1n p) (P0n q) = if ((comparePos p q) ≡ᵇ Lt) then Lt else Gt
comparePos (P1n p) P1      = Gt
comparePos (P0n p) (P1n q) = {!   !}
comparePos (P0n p) (P0n q) = comparePos p q
comparePos (P0n p) P1      = Gt
comparePos P1      (P1n q) = {!   !}
comparePos P1      (P0n q) = {!   !}
comparePos P1      P1      = Eq
-}
