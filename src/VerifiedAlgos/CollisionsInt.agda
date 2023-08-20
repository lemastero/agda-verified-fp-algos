{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

{-
Based on Software Foundations Vol 3 : Verified Functional Algoriths
by Andrew W. Appel

Chapter 12  Number Representations and Efficient Lookup Tables (Trie)
https://softwarefoundations.cis.upenn.edu/current/vfa-current/Trie.html
-}

module VerifiedAlgos.CollisionsInt where

open import Data.Bool
open import VerifiedAlgos.Int using (Int; z0; _≡Zᵇ_; sucZ)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

TotalMap = \ (A : Set) → Int → A

emptyMap : ∀ {A : Set} (default : A) → TotalMap A
emptyMap default x = default

update : ∀ {A : Set} (m : TotalMap A) (x : Int) (v : A) → TotalMap A
update m x v x1 = if (x ≡Zᵇ x1) then v else m x1

loop : List Int → Int → TotalMap Bool → Int
loop []       c table = c
loop (x ∷ xs) c table =
  if (table x)
  then loop xs (sucZ c) table
  else loop xs c (update table x true)

collisions : List Int → Int
collisions []       = z0
collisions input @ (x ∷ xs) = loop input z0 (emptyMap false)

-- TODO map nat2z
testCollisions : collisions (3 ∷ 1 ∷ 4 ∷ 1 ∷ 5 ∷ 9 ∷ 2 ∷ 6 ∷ []) ≡ 1
testCollisions = refl
