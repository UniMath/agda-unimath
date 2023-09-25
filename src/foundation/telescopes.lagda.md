# Telescopes

```agda
{-# OPTIONS --guardedness #-}

module foundation.telescopes where
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

A **telescope**, or **iterated type family**, is a list of type families
`(A₀, A₁, A₂, ..., A_n)` consisting of

- a type `A₀`,
- a type family `A₁ : A₀ → 𝒰`,
- a type family `A₂ : (x₀ : A₀) → A₁ x₀ → 𝒰`,
- ...
- a type family `A_n : (x₀ : A₀) ... (x_(n-1) : A_(n-1) x₀ ... x_(n-2)) → 𝒰`.

We say that a telescope `(A₀,...,A_n)` has **depth** `n+1`. In other words, the
depth of the telescope `(A₀,...,A_n)` is the length of the (dependent) list
`(A₀,...,A_n)`.

We encode the type of telescopes as a family of inductive types

```text
  telescope : (l : Level) → ℕ → UUω
```

The type of telescopes is a [directed tree](trees.directed-trees.md)

```text
  ... → T₃ → T₂ → T₁ → T₀,
```

where `T_n` is the type of all telescopes of depth `n`, and the map from
`T_(n+1)` to `T_n` maps `(A₀,...,A_n)` to `(A₀,...,A_(n-1))`. The type of such
directed trees can be defined as a coinductive record type, and we will define
the tree `T` of telescopes as a particular element of this tree.

## Definitions

### Telescopes

```agda
data
  telescope : (l : Level) → ℕ → UUω
  where
  base-telescope :
    {l1 : Level} → UU l1 → telescope l1 0
  cons-telescope :
    {l1 l2 : Level} {n : ℕ} {X : UU l1} →
    (X → telescope l2 n) → telescope (l1 ⊔ l2) (succ-ℕ n)
```
