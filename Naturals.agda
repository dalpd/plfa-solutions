module Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
   zero : ℕ
   suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- Exercise - Write out 7 in longhand.
x : ℕ
x = suc (suc (suc (suc (suc (suc (suc zero))))))

--  The definition of addition in Agda:
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

{- 
  0      + n  ≡  n           [1]
 (1 + m) + n  ≡  1 + (m + n) [2]
 (m + n) + p  ≡  m + (n + p) [3]

 [1]: zero is an identity for addition.
 [2]: Addition is associative.
 [3]: Most general form: Location of parentheses is irrelevant.
-}

p1 : 2 + 3 ≡ 5
p1 =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

p1' : 2 + 3 ≡ 5
p1' =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎
  
{-
 Agda is satisfied with the following:
 p1 : 2 + 3 ≡ 5
 p1 = refl

 A binary relation is said to be reflexive if every value relates to itself. 
 Evidence that a value is equal to itself is written refl.
-}

{-
 In p1 and p1' 2 + 3 ≡ 5 is a type.
 type -> proposition
 term -> evidence
-}

-- Exercise - Compute 3 + 4, writing out your reasoning as a chain of equations.
p2 : 3 + 4 ≡ 7
p2 =
  begin
    3 + 4
  ≡⟨⟩  -- inductive case
    suc (2 + 4)
  ≡⟨⟩  -- inductive case
    suc (suc (1 + 4))
  ≡⟨⟩  -- inductive case
    suc (suc (suc (0 + 4)))
  ≡⟨⟩  -- base case
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎
  
-- The definition of multiplication in Agda:
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

{-
  0      * n  ≡  0                 [4]
 (1 + m) * n  ≡  n + (m * n)       [5]
 (m + n) * p  ≡  (m * p) + (n * p) [6]

 [4]: zero property for multiplication.
 [5]: Multiplication distributes over addition.
 [6]: Most general form: [5] can be produced from [6], using 1 * n ≡ n
-}

p3 =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎

-- Exercise - Compute 3 * 4, writing out your reasoning as a chain of equations.

p4 =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎

-- Exercise - The definition of exponentiation in Agda:
_^_ : ℕ → ℕ → ℕ
n ^ zero = suc zero
n ^ suc m = n * (n ^ m)

p5 =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    81
 ∎

-- The definition of substraction in Agda:
_∸_ : ℕ → ℕ → ℕ
m       ∸ zero     = m
zero    ∸ (suc n) = zero -- since there are no negative natural numbers
(suc m) ∸ (suc n) = m ∸ n

p6 =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

p7 =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

-- Exercise - Compute 5 ∸ 3 and 3 ∸ 5, writing out your reasoning as a chain of equations.
p8 =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

p9 =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

infixl 6 _+_ _∸_
infixl 7 _*_


{-
 typed holes
 m ∘ n = ?
 _∘_ : ℕ → ℕ → ℕ
 zero  ∘ n = n
 suc zero ∘ n = suc {!!}
 suc (suc m) ∘ n = suc {!!}
-}

{-# BUILTIN NATPLUS  _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin
