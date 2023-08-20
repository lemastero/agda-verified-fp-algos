{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

{-
Based on Software Foundations Vol 3 : Verified Functional Algoriths
by Andrew W. Appel

Chapter 1  Basic Techniques for Comparisons and Permutations (Perm)
https://softwarefoundations.cis.upenn.edu/current/vfa-current/Perm.html

Coq standard library: https://github.com/coq/coq/blob/master/theories/PArith/BinPosDef.v
Agda-stdlib: https://github.com/agda/agda-stdlib/blob/master/src/Data/List/Relation/Binary/Permutation/Propositional.agda
-}

module Permutation where

open import Data.Nat using (suc)
open import Data.List using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Permutation {A : Set} : List A → List A → Set where
  permNil : Permutation [] []
  permSkip : ∀ (x : A) (xs xs' : List A)
           → Permutation xs xs'
           → Permutation (x ∷ xs) (x ∷ xs')
  permSwap : ∀ (x y : A) (xs : List A)
           → Permutation (y ∷ x ∷ xs) (x ∷ y ∷ xs)
  permTrans : ∀ (xs ys zs : List A)
            → Permutation xs ys → Permutation ys zs
            → Permutation xs zs

lengthAppendSuc : ∀ {A : Set} (xs : List A) (a : A)
               → length (a ∷ xs) ≡ suc (length xs)
lengthAppendSuc xs a = refl

permLen : ∀ {A : Set} (xs ys : List A) (p : Permutation xs ys)
        → length xs ≡ length ys
permLen .[] .[] permNil = refl
permLen .(x ∷ xs) .(x ∷ xs') ps @ (permSkip x xs xs' p)
  rewrite lenghAppendSuc xs x
  | permLen xs xs' p = refl
permLen .(y ∷ x ∷ xs) .(x ∷ y ∷ xs) (permSwap x y xs) = refl
permLen xs ys (permTrans .xs zs .ys p1 p2)
  rewrite permLen xs zs p1 = permLen zs ys p2

permSym : ∀ {A : Set} (xs ys : List A) (p : Permutation xs ys)
       → Permutation ys xs
permSym .[] .[] permNil = permNil
permSym .(x ∷ xs) .(x ∷ xs')
        (permSkip x xs xs' p) =
         permSkip x xs' xs (permSym xs xs' p)
permSym .(y ∷ x ∷ xs) .(x ∷ y ∷ xs)
        (permSwap x y xs) =
         permSwap y x xs
permSym xs zs
        (permTrans .xs ys .zs p1 p2) =
        permTrans zs ys xs (permSym ys zs p2) (permSym xs ys p1)
