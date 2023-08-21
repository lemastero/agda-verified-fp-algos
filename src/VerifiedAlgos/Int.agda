{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

{-
Based on Software Foundations Vol 3 : Verified Functional Algoriths
by Andrew W. Appel

Chapter 12  Number Representations and Efficient Lookup Tables (Trie)
https://softwarefoundations.cis.upenn.edu/current/vfa-current/Maps.html
-}

module VerifiedAlgos.Int where

open import Data.Bool using (Bool; true; false)
open import VerifiedAlgos.Positive using (Pos; P1; P0n; P1n
  ; sucPos; _≡Posᵇ_; p2x-1; _+P_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Int : Set where
  z0 : Int
  zPos : Pos → Int
  zNeg : Pos → Int

sucZ : Int → Int
sucZ z0             = zPos P1
sucZ (zPos p)       = zPos (sucPos p)
sucZ (zNeg P1)      = z0
sucZ (zNeg (P1n p)) = zNeg (P0n p)   -- -(1+2p) + 1 = -2p
sucZ (zNeg (P0n p)) = zNeg (p2x-1 p) -- -2p + 1 = -(2p-1)

_*2Z : Int → Int
z0     *2Z = z0
zPos p *2Z = zPos (p *2P)
zNeg p *2Z = zNeg (p *2P)

negZ : Int → Int
negZ z0       = z0
negZ (zPos x) = zNeg x
negZ (zNeg x) = zPos x

negZ-involutive : ∀ (n : Int) → negZ (negZ n) ≡ n
negZ-involutive z0       = refl
negZ-involutive (zPos x) = refl
negZ-involutive (zNeg x) = refl

_-P_ : Pos → Pos → Int
P1n a -P P1    = zPos (P0n a)
P0n a -P P1    = zPos (p2x-1 a)
P1    -P P1    = z0
P1    -P P1n b = zNeg (P0n b)
P1    -P P0n b = zNeg (p2x-1 b)
P1n a -P P1n b = (a -P b) *2Z -- 1+2*a - (1+2*b) = 2 (a-b)
P0n a -P P0n b = (a -P b) *2Z -- 2*a - 2*b = 2*(a-b)
P0n a -P P1n b = negZ (sucZ ((a -P b) *2Z)) -- 2a - 1+2b =  2(a-b) -1 = -1 * (2*(b-a)+1)
P1n a -P P0n b = sucZ ((a -P b) *2Z) -- 1+2a - 2*b = 1+(2*(a-b))

_+Z_ : Int → Int → Int
a        +Z z0       = a
z0       +Z (zPos b) = zPos b
z0       +Z (zNeg b) = zNeg b
(zPos a) +Z (zPos b) = zPos (a +P b)
(zNeg a) +Z (zNeg b) = zNeg (a +P b)
(zNeg a) +Z (zPos b) = b -P a
(zPos a) +Z (zNeg b) = a -P b

_≡Zᵇ_ : Int → Int → Bool
z0     ≡Zᵇ z0     = true
z0     ≡Zᵇ zPos x = false
z0     ≡Zᵇ zNeg x = false
zPos x ≡Zᵇ z0     = false
zPos x ≡Zᵇ zNeg y = false
zNeg x ≡Zᵇ z0     = false
zNeg x ≡Zᵇ zPos y = false
zPos x ≡Zᵇ zPos y = x ≡Posᵇ y
zNeg x ≡Zᵇ zNeg y = x ≡Posᵇ y
