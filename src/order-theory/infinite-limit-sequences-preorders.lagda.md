# Sequences in preorders tending to infinity

```agda
module order-theory.infinite-limit-sequences-preorders where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.sequences
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.preorders
open import order-theory.sequences-preorders
```

</details>

## Idea

A [sequence ](order-theory.sequences-preorders.md) `u` in a
[preorder](order-theory.preorders.md) `P`
{{#concept "tends to infinity" Disambiguation="sequence in a preorder" Agda=is-limit-∞-sequence-Preorder}}
if there exists a map `m : P → ℕ` such that whenever `m x ≤ n` in `ℕ`, `x ≤ u n`
in `P`. The map `m` is called a limit-modulus of `u` at infinity.

## Definitions

### The predicate of tending to infinity

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  (u : type-sequence-Preorder P)
  where

  is-modulus-limit-∞-prop-sequence-Preorder :
    (type-Preorder P → ℕ) → Prop (l1 ⊔ l2)
  is-modulus-limit-∞-prop-sequence-Preorder m =
    Π-Prop
      ( type-Preorder P)
      ( λ x →
        Π-Prop
          ( ℕ)
          ( λ n →
            leq-ℕ-Prop (m x) n ⇒
            leq-prop-Preorder P x (u n)))

  is-modulus-limit-∞-sequence-Preorder : (type-Preorder P → ℕ) → UU (l1 ⊔ l2)
  is-modulus-limit-∞-sequence-Preorder m =
    type-Prop (is-modulus-limit-∞-prop-sequence-Preorder m)

  modulus-limit-∞-sequence-Preorder : UU (l1 ⊔ l2)
  modulus-limit-∞-sequence-Preorder =
    type-subtype is-modulus-limit-∞-prop-sequence-Preorder

  modulus-modulus-limit-∞-sequence-Preorder :
    modulus-limit-∞-sequence-Preorder → type-Preorder P → ℕ
  modulus-modulus-limit-∞-sequence-Preorder = pr1

  is-modulus-modulus-limit-∞-sequence-Preorder :
    (m : modulus-limit-∞-sequence-Preorder) →
    is-modulus-limit-∞-sequence-Preorder
      (modulus-modulus-limit-∞-sequence-Preorder m)
  is-modulus-modulus-limit-∞-sequence-Preorder = pr2

  is-limit-∞-prop-sequence-Preorder : Prop (l1 ⊔ l2)
  is-limit-∞-prop-sequence-Preorder =
    is-inhabited-subtype-Prop is-modulus-limit-∞-prop-sequence-Preorder

  is-limit-∞-sequence-Preorder : UU (l1 ⊔ l2)
  is-limit-∞-sequence-Preorder = type-Prop is-limit-∞-prop-sequence-Preorder
```

### Sequences in preorders tending to infinity

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  limit-∞-sequence-Preorder : UU (l1 ⊔ l2)
  limit-∞-sequence-Preorder = type-subtype (is-limit-∞-prop-sequence-Preorder P)

  seq-limit-∞-sequence-Preorder :
    limit-∞-sequence-Preorder → type-sequence-Preorder P
  seq-limit-∞-sequence-Preorder = pr1

  is-limit-∞-seq-limit-∞-sequence-Preorder :
    (u : limit-∞-sequence-Preorder) →
    is-limit-∞-sequence-Preorder P (seq-limit-∞-sequence-Preorder u)
  is-limit-∞-seq-limit-∞-sequence-Preorder = pr2
```

## Properties

### The subtype of sequences tending to infinity is upward closed

Given to sequences `u ≤ v`, if `u` tends to infinity, so does `v`.

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  (u v : type-sequence-Preorder P) (I : leq-sequence-Preorder P u v)
  where

  modulus-leq-modulus-limit-∞-sequence-Preorder :
    modulus-limit-∞-sequence-Preorder P u →
    modulus-limit-∞-sequence-Preorder P v
  modulus-leq-modulus-limit-∞-sequence-Preorder =
    tot
      ( λ N Mu x n J →
        transitive-leq-Preorder P
          ( x)
          ( u n)
          ( v n)
          ( I n)
          ( Mu x n J))

  is-upward-closed-limit-∞-sequence-Preorder :
    is-limit-∞-sequence-Preorder P u → is-limit-∞-sequence-Preorder P v
  is-upward-closed-limit-∞-sequence-Preorder =
    map-is-inhabited modulus-leq-modulus-limit-∞-sequence-Preorder
```
