{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

{-
Based on Software Foundations Vol 3 : Verified Functional Algoriths
by Andrew W. Appel

Chapter 8  Binary Search Trees (SearchTree)
https://softwarefoundations.cis.upenn.edu/current/vfa-current/SearchTree.html
-}

module VerifiedAlgos.BST where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; _<ᵇ_)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _++_) renaming (_∷_ to _::_)
open import Data.Product using (_×_; _,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_)
open import Relation.Nullary.Negation using (¬_)


_>ᵇ_ : ℕ → ℕ → Bool
n >ᵇ m = m <ᵇ n

-- TODO generalize to preorder
-- TODO move to module parameter or another argument
Key = ℕ

-- binary search tree (values in the nodes)
---------------------
data Tree (V : Set) : Set where
  emptyTree : Tree V
  tree : Tree V        -- left subtree
      -> Key -> V      -- mapping k->v in current node
      -> (r : Tree V)  -- right subtree
      -> Tree V

-- TODO generalize to Decidable
isBound : {V : Set} → Key → Tree V → Bool
isBound k emptyTree         = false
isBound k (tree tl k2 v tr) =
  if k <ᵇ k2
  then isBound k tl
  else (
    if k >ᵇ k2
    then isBound k tr
    else true )
{-
isBound k (tree tl k2 v tr) with k <ᵇ k2
...  | true  = isBound k tl
...  | false with k >ᵇ k2
...          | true  = isBound k tr
...          | false = true
-}

lookup : {V : Set} → (default : V) → Key → Tree V → V
lookup d k emptyTree        = d
lookup d k (tree tl k2 x tr) with k <ᵇ k2
...  | true  = lookup d k tl
...  | false with k >ᵇ k2
...    | true  = lookup d k tr
...    | false = x

insert : {V : Set} → Key → V → Tree V → Tree V
insert k v emptyTree = tree emptyTree k v emptyTree
insert k v (tree tl k2 v2 tr) with k <ᵇ k2
              -- insert into left subtree
... | true  = tree (insert k v tl) k2 v2 tr
... | false with k >ᵇ k2
                -- insert into right subtree
...   | true  = tree tl k2 v2 (insert k v tr)
...   | false = tree tl k v tr  -- replace

-- TODO map
-- TODO traverse

{-

    4 -> "four"

2 -> "two"    5 -> "five"

-}
testTree : Tree String
testTree = tree (tree emptyTree 2 "two" emptyTree) 4 "four" (tree emptyTree 5 "five" emptyTree)

testInsert : insert 5 "five"
               (insert 2 "two"
                  (insert 4 "four" emptyTree)) ≡ testTree
testInsert = refl

testLookup1 : lookup "" 5 testTree ≡ "five"
testLookup1 = refl

testLookup2 : lookup "" 3 testTree ≡ ""
testLookup2 = refl

testIsBound : isBound 3 testTree ≡ false
testIsBound = refl

testNotBST : Tree String
testNotBST = tree (tree emptyTree 5 "five" emptyTree)
                  4 "four"
                  (tree emptyTree 2 "two" emptyTree)

testLookupFailsOnNonBST : (lookup "" 2 testNotBST) ≢ "two"
testLookupFailsOnNonBST ()

-- property that holds for every element in the Tree
----------------------------------------------------
data AllTree {V : Set} (P : Key → V → Set) : Tree V → Set where
  emptyTree : AllTree P emptyTree
  tree      : ∀ {tl : Tree V} {k : Key} {v : V} {tr : Tree V}
             → AllTree P tl
             → P k v
             → AllTree P tr
             → AllTree P (tree tl k v tr)

-- TODO replace with sth from std lib
T : Bool → Set
T true  = ⊤
T false = ⊥

-- binary search tree invariant
-------------------------------
data BST {V : Set} : Tree V → Set where
  BSTEmpty : BST emptyTree
  BSTTree  : ∀ {tl : Tree V} {k : Key} {v : V} {tr : Tree V}
             → AllTree (λ k2 _ → T (k2 <ᵇ k)) tl
             → AllTree (λ k2 _ → T (k2 >ᵇ k)) tr
             → BST tl
             → BST tr
             → BST (tree tl k v tr)

testBST5 : BST (tree emptyTree 5 "five" emptyTree)
testBST5 = BSTTree emptyTree emptyTree BSTEmpty BSTEmpty

testBST2 : BST (tree emptyTree 2 "two" emptyTree)
testBST2 = BSTTree emptyTree emptyTree BSTEmpty BSTEmpty

testBST : BST testTree
testBST = BSTTree (tree emptyTree tt emptyTree)
                  (tree emptyTree tt emptyTree)
                  testBST2 testBST5

{-
-- TODO do I need to give up here (switch to Bool predicate ?)
testNonBST : BST testNotBST
testNonBST = BSTTree (tree emptyTree {!   !} emptyTree)
                     (tree emptyTree {!  !} emptyTree)
                     testBST5 testBST2
-}

-- TODO this seems wrong we shoul have invariant with insert
-- make sure it holds for it
-- and then every tree created from insert would maintain it
-- alternatively do it on the constructors for Tee

-- TODO insert and BST property

-- properties
-------------------
lookup-correct-1 : ∀ {K V : Set} {k : Key} {d : V}
            → lookup d k emptyTree ≡ d
lookup-correct-1 = refl

{-
lemma : {K V : Set} {k : Key} {d v : V} {t : Tree V}
      → (lookup d k (tree emptyTree k v emptyTree)) ≡ v
lemma = {!   !}

lookup-correct-2 : ∀ {K V : Set} {k : Key} {d v : V} {t : Tree V}
            → lookup d k (insert k v t) ≡ v
lookup-correct-2 {K} {V} {k} {d} {v} {emptyTree} with k <ᵇ k
... | true = {! refl  !} -- TODO here I need decidable to exclude this case
... | false = {! refl  !}
lookup-correct-2 {K} {V} {k} {d} {v} {tree t x x₁ t₁} = {!   !}

lookup-correct-3 : ∀ {K V : Set} {k : Key} {k2 : Key} {d v : V} {t : Tree V}
            → ¬ (k ≡ k2)
            → lookup d k2 (insert k v t) ≡ lookup d k2 t
lookup-correct-3 = {!   !}
-}

-- TODO isBound correctness theorems

-- TODO if isBound == false then lookup returns default

-- TODO general map properties

treeElements : {V : Set} (t : Tree V) → List (Key × V)
treeElements emptyTree        = []
treeElements (tree tl k v tr) = (treeElements tl)
                                ++ (k , v) :: (treeElements tr)

treeElements2 : ∀ {V : Set} (t : Tree V)
              → (acc : List (Key × V))
              → List (Key × V)
treeElements2 emptyTree        acc = acc
treeElements2 (tree tl k v tr) acc = treeElements2 tl ( (k , v) :: treeElements2 tr acc )
