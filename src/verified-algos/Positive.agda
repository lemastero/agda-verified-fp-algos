{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

{-
Based on Software Foundations Vol 3 : Verified Functional Algoriths
by Andrew W. Appel

Chapter 12  Number Representations and Efficient Lookup Tables (Trie)
https://softwarefoundations.cis.upenn.edu/current/vfa-current/Maps.html
-}

module verified-algos.Positive where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

psuc : Pos → Pos
psuc (P1n p) = P0n (psuc p)
psuc (P0n p) = P1n p
psuc P1      = P0n P1

padd : Pos → Pos → Pos
padd = {!   !}

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
