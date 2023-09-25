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

An **iterated type family** is a list of type families `(A₀, A₁, A₂, ..., A_n)`
consisting of

- a type `A₀`,
- a type family `A₁ : A₀ → 𝒰`,
- a type family `A₂ : (x₀ : A₀) → A₁ x₀ → 𝒰`,
- ...
- a type family `A_n : (x₀ : A₀) ... (x_(n-1) : A_(n-1) x₀ ... x_(n-2)) → 𝒰`.

We say that an iterated type family `(A₀,...,A_n)` has **depth** `n+1`. In other
words, the depth of the iterated type family `(A₀,...,A_n)` is the length of the
(dependent) list `(A₀,...,A_n)`.

We encode the type of iterated type families as a family of inductive types

```text
  iterated-type-family : (l : Level) → ℕ → UUω
```

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
  iterated-type-family : (l : Level) → ℕ → UUω
  where
  base-iterated-type-family :
    {l1 : Level} → UU l1 → iterated-type-family l1 0
  cons-iterated-type-family :
    {l1 l2 : Level} {n : ℕ} {X : UU l1} →
    (X → iterated-type-family l2 n) →
    iterated-type-family (l1 ⊔ l2) (succ-ℕ n)
```
