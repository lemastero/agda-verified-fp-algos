{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

{-
Based on Software Foundations Vol 3 : Verified Functional Algoriths
by Andrew W. Appel

Chapter 7  Total and Partial Maps (Maps)
https://softwarefoundations.cis.upenn.edu/current/vfa-current/Maps.html
-}

module verified-algos.Maps where

open import Data.Nat using (ℕ; _≡ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (Bool; true; false; if_then_else_)

TotalMap = \ (A : Set) → ℕ → A

emptyMap : {A : Set} (v : A) → TotalMap A
emptyMap v x = v

update : {A : Set} (m : TotalMap A) (x : ℕ) (v : A)
     → TotalMap A
update m x v x1 = if (x ≡ᵇ x1) then v else m x1
