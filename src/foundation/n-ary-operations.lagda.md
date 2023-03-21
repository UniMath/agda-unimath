# n-ary operations

```agda
module foundation.n-ary-operations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given `n` types, an n-ary operation on them is a function that takes as inputs
one element of each type, and returs an element in some type `X`.

## Definitions

```agda
max-level :
  (n : ℕ)
  (I : functional-vec Level n) →
  Level
max-level zero-ℕ I = lzero
max-level (succ-ℕ n) I =
  I ( neg-one-Fin n) ⊔
    ( max-level n (λ i → I (inl-Fin n i)))

n-ary-operation :
  (n : ℕ)
  (I : Fin n → Level)
  (As : (i : Fin n) → UU (I i))
  {l : Level} (X : UU l) →
  UU (l ⊔ max-level n I)
n-ary-operation zero-ℕ I As X = X
n-ary-operation (succ-ℕ n) I As X =
  As ( neg-one-Fin n) →
  n-ary-operation n
    ( tail-functional-vec n I)
    ( λ i → As (inl-Fin n i))
    X

apply-n-ary-operation :
  (n : ℕ)
  (I : Fin n → Level)
  (As : (i : Fin n) → UU (I i))
  {l : Level} (X : UU l) →
  n-ary-operation n I As X →
  ((i : Fin n) → As i) →
  X
apply-n-ary-operation zero-ℕ I As X f as = f
apply-n-ary-operation (succ-ℕ n) I As X f as =
  apply-n-ary-operation n
    ( tail-functional-vec n I)
    ( λ i → As (inl-Fin n i))
    ( X)
    ( f (as (neg-one-Fin n)))
    ( λ i → as (inl-Fin n i))
```
