{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

{-
Based on Software Foundations vol 3 Verified Alorithms
by Andrew W. Appel
https://softwarefoundations.cis.upenn.edu/vfa-current/index.html

Chapter 11  Red-Black Trees (Redblack)
https://softwarefoundations.cis.upenn.edu/current/vfa-current/Redblack.html
-}

module verified-algos.RedBlackTree where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; _<ᵇ_)
open import Data.List using (List; []) renaming (_∷_ to _::_)
open import Data.Product using (_×_; _,_)
open import Function.Base using (case_of_)

Key = ℕ

data Color : Set where
  Red   : Color
  Black : Color

data RedBlackTree (V : Set) : Set where
  EmptyRBT : RedBlackTree V
  RBT      : (c : Color)
           → (left : RedBlackTree V)
           → (k : Key)
           → (val : V)
           → (right : RedBlackTree V)
           → RedBlackTree V

lookup : {V : Set}
       → (default : V)
       → Key
       → RedBlackTree V
       ----------------
       → V
lookup defaultVal key EmptyRBT                     = defaultVal
lookup defaultVal key (RBT c left currKey x right) =
  if key <ᵇ currKey
  then lookup defaultVal key left
  else (
    if currKey <ᵇ key
    then lookup defaultVal key right
    else x)

balance : {V : Set}
        → Color
        → RedBlackTree V
        → Key
        → V
        → RedBlackTree V
        → RedBlackTree V
balance Red   tl  k vk tr = RBT Red tl k vk tr
balance Black tl  k vk tr = checkL tl vk tr
  where
    checkR : {V : Set}
               → RedBlackTree V → V → RedBlackTree V
               → RedBlackTree V

    -- if Red Red t
    checkR tl vk (RBT Red (RBT Red b y vy tr2) z vz tr3) =
      RBT Red (RBT Black tl k vk b) y vy (RBT Black tr2 z vz tr3)
    -- if Red t Red
    checkR tl vk (RBT Red b@EmptyRBT            y vy (RBT Red tl2 z vz tr2)) =
      RBT Red (RBT Black tl k vk b) y vy (RBT Black tl2 z vz tr2)
    checkR tl vk (RBT Red b@(RBT Black _ _ _ _) y vy (RBT Red tl2 z vz tr2)) =
      RBT Red (RBT Black tl k vk b) y vy (RBT Black tl2 z vz tr2)
    -- otherwise insert here as Black
    checkR tl vk tr@(RBT Red (RBT Black _ _ _ _) _ _ EmptyRBT) =
      RBT Black tl k vk tr
    checkR tl vk tr@(RBT Red (RBT Black _ _ _ _) _ _ (RBT Black _ _ _ _)) =
      RBT Black tl k vk tr
    checkR tl vk tr@(RBT Red EmptyRBT            _ _ EmptyRBT) =
      RBT Black tl k vk tr
    checkR tl vk tr@(RBT Red EmptyRBT            _ _ (RBT Black _ _ _ _)) =
      RBT Black tl k vk tr
    checkR tl vk tr@(RBT Black _ _ _ _) = RBT Black tl k vk tr
    checkR tl vk EmptyRBT               = RBT Black tl k vk EmptyRBT

    checkL : {V : Set}
           → RedBlackTree V → V → RedBlackTree V
           → RedBlackTree V
    -- if Red Red t
    checkL (RBT Red (RBT Red a x vx b) y vy c) vk tr =
      RBT Red (RBT Black a x vx b) y vy c
    -- if Red t Red
    checkL (RBT Red (a @ (RBT Black _ _ _ _)) x vx (RBT Red b y vy c)) vk tr =
       RBT Red (RBT Black a x vx b) y vy (RBT Black c k vk tr)
    checkL (RBT Red (a @ EmptyRBT)            x vx (RBT Red b y vy c)) vk tr =
       RBT Red (RBT Black a x vx b) y vy (RBT Black c k vk tr)
    -- otherwise check right tree
    checkL tl@(RBT Red EmptyRBT            _ _ (RBT Black _ _ _ _)) = checkR tl
    checkL tl@(RBT Red (RBT Black _ _ _ _) _ _ (RBT Black _ _ _ _)) = checkR tl
    checkL tl@(RBT Red (RBT Black _ _ _ _) _ _ EmptyRBT)            = checkR tl
    checkL tl@(RBT Red EmptyRBT            _ _ EmptyRBT)            = checkR tl
    checkL tl@(RBT Black _ _ _ _)                                   = checkR tl
    checkL tl@EmptyRBT                                              = checkR tl

ins : {V : Set}
    → Key → V → RedBlackTree V
    → RedBlackTree V
ins key val EmptyRBT            = RBT Red EmptyRBT key val EmptyRBT
ins key val (RBT c tl k2 v2 tr) =
  if key <ᵇ k2
  then balance c (ins key val tl) k2 v2 tr
  else (
    if k2 <ᵇ key
    then balance c tl k2 v2 (ins key val tr)
    else (RBT c tl key val tr))

makeBlack : {V : Set} → RedBlackTree V → RedBlackTree V
makeBlack EmptyRBT            = EmptyRBT
makeBlack (RBT c tl k val tr) = RBT Black tl k val tr

insert : {V : Set}
       → Key → V
       → RedBlackTree V
       → RedBlackTree V
insert k val t = makeBlack (ins k val t)

elements : {V : Set} → RedBlackTree V → List (Key × V)
elements t = helper t []
  where
    helper : {V : Set} → RedBlackTree V → List (Key × V) → List (Key × V)
    helper EmptyRBT            acc = acc
    helper (RBT c tl k val tr) acc = helper tl ((k , val) :: helper tr acc)
