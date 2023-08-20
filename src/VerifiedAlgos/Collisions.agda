{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

{-
Based on Software Foundations Vol 3 : Verified Functional Algoriths
by Andrew W. Appel

Chapter 12  Number Representations and Efficient Lookup Tables (Trie)
https://softwarefoundations.cis.upenn.edu/current/vfa-current/Maps.html
-}

module VerifiedAlgos.Collisions where

open import Data.Bool
open import Data.Nat using (ℕ; suc)
open import Data.List
open import VerifiedAlgos.Maps using (TotalMap; emptyMap; update)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

loop : List ℕ → ℕ → TotalMap Bool → ℕ
loop []       c table = c
loop (x ∷ xs) c table =
  if (table x)
  then loop xs (suc c) table
  else loop xs c (update table x true)

collisions : List ℕ → ℕ
collisions []       = 0
collisions input @ (x ∷ xs) = loop input 0 (emptyMap false)

testCollisions : collisions (3 ∷ 1 ∷ 4 ∷ 1 ∷ 5 ∷ 9 ∷ 2 ∷ 6 ∷ []) ≡ 1
testCollisions = refl
