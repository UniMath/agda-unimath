# Iterated type families

```agda
{-# OPTIONS --guardedness #-}

module foundation.iterated-type-families where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists

open import trees.universal-tree
```

</details>

## Idea

An **iterated type family** is a sequence of type families
`(A₀, A₁, A₂, ..., A_n)` consisting of

- a type `A₀`,
- a type family `A₁ : A₀ → 𝒰`,
- a type family `A₂ : (x₀ : A₀) → A₁ x₀ → 𝒰`,
- ...
- a type family `A_n : (x₀ : A₀) ... (x_(n-1) : A_(n-1) x₀ ... x_(n-2)) → 𝒰`.

We say that an iterated type family `(A₀,...,A_n)` has **depth** `n+1`. In other
words, the depth of the iterated type family `(A₀,...,A_n)` is the length of the
(dependent) list `(A₀,...,A_n)`.

The type of iterated type families is a [directed tree](trees.directed-trees.md)

```text
  ... → T₃ → T₂ → T₁ → T₀,
```

where `T_n` is the type of all iterated type families of depth `n`, and the map
from `T_(n+1)` to `T_n` maps `(A₀,...,A_n)` to `(A₀,...,A_(n-1))`. The type of
such directed trees can be defined as a coinductive record type, and we will
define the tree `T` of iterated type families as a particular element of this
tree.

## Definitions

### Iterated type families

```agda
data
  Iterated-Type-Family : (l : Level) → ℕ → UUω
  where
  nil-Iterated-Type-Family : Iterated-Type-Family lzero 0
  base-Iterated-Type-Family :
    {l1 : Level} → UU l1 → Iterated-Type-Family l1 1
  cons-Iterated-Type-Family :
    {l1 l2 : Level} {n : ℕ} {X : UU l1} →
    (X → Iterated-Type-Family l2 (succ-ℕ n)) →
    Iterated-Type-Family (l1 ⊔ l2) (succ-ℕ (succ-ℕ n))
```

### Iterated dependent products of iterated type families

```agda
Π-Iterated-Type-Family :
  {l : Level} {n : ℕ} → Iterated-Type-Family l n → UU l
Π-Iterated-Type-Family nil-Iterated-Type-Family = unit
Π-Iterated-Type-Family (base-Iterated-Type-Family A) = A
Π-Iterated-Type-Family (cons-Iterated-Type-Family {X = X} A) =
  (x : X) → Π-Iterated-Type-Family (A x)
```

### Testing iterated type families

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  where

  test :
    Π-Iterated-Type-Family
      ( cons-Iterated-Type-Family
        ( λ x → cons-Iterated-Type-Family
          ( λ y → base-Iterated-Type-Family (C x y)))) ＝
    ( (x : A) (y : B x) → C x y)
  test = refl 
```
