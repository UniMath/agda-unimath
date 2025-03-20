# Bounded multisets

```agda
open import foundation.function-extensionality-axiom

module
  trees.bounded-multisets
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types funext
open import foundation.existential-quantification funext
open import foundation.propositions funext
open import foundation.universe-levels

open import trees.empty-multisets funext
open import trees.multisets funext
open import trees.w-types funext
```

</details>

## Idea

A [multiset](trees.multisets.md) `X` is said to be of **natural height** `0` if
`X` has no elements, and of natural height `n+1` if every
[element](trees.elementhood-relation-w-types.md) in `X` is of natural height
`n`. Multisets of finite natural height are said to be **naturally bounded**.

Note that finite multisets, which consist of finitely many elements, each of
which are finite multisets, are automatically naturally bounded. Nonfinite
multisets, however, need not be naturally bounded.

We also note that there should exist a more general notion of height, in which
heights are measured by upwards closed subsets of the natural numbers. This is
why we speak of _naturally_ bounded multisets here. On the other hand, every
multiset is bounded in this more general sense, and this bound is unique.

## Definitions

### The predicate of being a multiset of natural height `n`

```agda
module _
  {l : Level}
  where

  is-of-natural-height-𝕍 : ℕ → 𝕍 l → UU l
  is-of-natural-height-𝕍 zero-ℕ X =
    is-empty-𝕍 X
  is-of-natural-height-𝕍 (succ-ℕ n) (tree-𝕎 X Y) =
    (x : X) → is-of-natural-height-𝕍 n (Y x)

  is-prop-is-of-natural-height-𝕍 :
    (n : ℕ) (X : 𝕍 l) → is-prop (is-of-natural-height-𝕍 n X)
  is-prop-is-of-natural-height-𝕍 zero-ℕ = is-property-is-empty-𝕍
  is-prop-is-of-natural-height-𝕍 (succ-ℕ n) (tree-𝕎 X Y) =
    is-prop-Π (λ x → is-prop-is-of-natural-height-𝕍 n (Y x))

  is-of-natural-height-prop-𝕍 : ℕ → 𝕍 l → Prop l
  is-of-natural-height-prop-𝕍 n X =
    ( is-of-natural-height-𝕍 n X , is-prop-is-of-natural-height-𝕍 n X)
```

### Explicitly bounded multisets

An **explicitly bounded multiset** is a multiset of specified natural height.
Note that, as we will show below, every multiset of natural height `n` is also a
multiset of natural height `n + 1`, so the type of natural numbers `n` equipped
with a proof that `X` is of natural height `n` is far from a proposition.

```agda
Explicitly-Bounded-𝕍 : (l : Level) → UU (lsuc l)
Explicitly-Bounded-𝕍 l =
  Σ (𝕍 l) (λ X → Σ ℕ (λ n → is-of-natural-height-𝕍 n X))
```

### Bounded multisets

A **bounded multiset** is a multiset for which a natural bound
[merely exists](foundation.existential-quantification.md)

```agda
data
  Bounded-𝕍 (l : Level) : ℕ → UU (lsuc l)
  where
  empty-multiset-Bounded-𝕍 : Bounded-𝕍 l 0
  tree-multiset-Bounded-𝕍 :
    {n : ℕ} {X : UU l} (Y : X → Bounded-𝕍 l n) → Bounded-𝕍 l (succ-ℕ n)

Bounded-𝕍' : (l : Level) → UU (lsuc l)
Bounded-𝕍' l =
  Σ (𝕍 l) (λ X → exists ℕ (λ n → is-of-natural-height-prop-𝕍 n X))
```

## Properties

### The empty multiset is of any natural height

```agda
module _
  {l : Level}
  where

  is-of-natural-height-is-empty-𝕍 :
    (n : ℕ) (X : 𝕍 l) → is-empty-𝕍 X → is-of-natural-height-𝕍 n X
  is-of-natural-height-is-empty-𝕍 zero-ℕ X H = H
  is-of-natural-height-is-empty-𝕍 (succ-ℕ n) (tree-𝕎 X Y) H x = ex-falso (H x)
```

### A multiset of natural height `n` is a multiset of natural height `n + 1`

```agda
module _
  {l : Level}
  where

  is-of-natural-height-succ-𝕍 :
    (n : ℕ) (X : 𝕍 l) →
    is-of-natural-height-𝕍 n X → is-of-natural-height-𝕍 (succ-ℕ n) X
  is-of-natural-height-succ-𝕍 zero-ℕ X H =
    is-of-natural-height-is-empty-𝕍 1 X H
  is-of-natural-height-succ-𝕍 (succ-ℕ n) (tree-𝕎 X Y) H x =
    is-of-natural-height-succ-𝕍 n (Y x) (H x)
```
