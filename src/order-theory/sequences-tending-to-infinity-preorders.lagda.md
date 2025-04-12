# Sequences in preorders tending to infinity

```agda
module order-theory.sequences-tending-to-infinity-preorders where
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

A [sequence](order-theory.sequences-preorders.md) `u` in a
[preorder](order-theory.preorders.md) `P`
{{#concept "tends to infinity" Disambiguation="sequence in a preorder" Agda=tends-to-infinity-sequence-Preorder}}
if there exists a map `m : P → ℕ` such that whenever `m x ≤ n` in `ℕ`, `x ≤ u n`
in `P`. The map `m` is called a limit-modulus of `u` at infinity.

## Definitions

### The predicate of tending to infinity

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  (u : type-sequence-Preorder P)
  where

  is-modulus-tends-to-infinity-prop-sequence-Preorder :
    (type-Preorder P → ℕ) → Prop (l1 ⊔ l2)
  is-modulus-tends-to-infinity-prop-sequence-Preorder m =
    Π-Prop
      ( type-Preorder P)
      ( λ x →
        Π-Prop
          ( ℕ)
          ( λ n →
            leq-ℕ-Prop (m x) n ⇒
            leq-prop-Preorder P x (u n)))

  is-modulus-tends-to-infinity-sequence-Preorder :
    (type-Preorder P → ℕ) → UU (l1 ⊔ l2)
  is-modulus-tends-to-infinity-sequence-Preorder m =
    type-Prop (is-modulus-tends-to-infinity-prop-sequence-Preorder m)

  modulus-tends-to-infinity-sequence-Preorder : UU (l1 ⊔ l2)
  modulus-tends-to-infinity-sequence-Preorder =
    type-subtype is-modulus-tends-to-infinity-prop-sequence-Preorder

  modulus-modulus-tends-to-infinity-sequence-Preorder :
    modulus-tends-to-infinity-sequence-Preorder → type-Preorder P → ℕ
  modulus-modulus-tends-to-infinity-sequence-Preorder = pr1

  is-modulus-modulus-tends-to-infinity-sequence-Preorder :
    ( m : modulus-tends-to-infinity-sequence-Preorder) →
    ( is-modulus-tends-to-infinity-sequence-Preorder
      ( modulus-modulus-tends-to-infinity-sequence-Preorder m))
  is-modulus-modulus-tends-to-infinity-sequence-Preorder = pr2

  subtype-tends-to-infinity-sequence-Preorder : Prop (l1 ⊔ l2)
  subtype-tends-to-infinity-sequence-Preorder =
    is-inhabited-subtype-Prop
      is-modulus-tends-to-infinity-prop-sequence-Preorder

  tends-to-infinity-sequence-Preorder : UU (l1 ⊔ l2)
  tends-to-infinity-sequence-Preorder =
    type-Prop subtype-tends-to-infinity-sequence-Preorder
```

### Sequences in preorders tending to infinity

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  type-sequence-tending-to-infinity-Preorder : UU (l1 ⊔ l2)
  type-sequence-tending-to-infinity-Preorder =
    type-subtype (subtype-tends-to-infinity-sequence-Preorder P)

  seq-tending-to-infinity-sequence-Preorder :
    type-sequence-tending-to-infinity-Preorder → type-sequence-Preorder P
  seq-tending-to-infinity-sequence-Preorder = pr1

  tends-to-infinity-seq-tending-to-infinity-sequence-Preorder :
    (u : type-sequence-tending-to-infinity-Preorder) →
    tends-to-infinity-sequence-Preorder
      ( P)
      ( seq-tending-to-infinity-sequence-Preorder u)
  tends-to-infinity-seq-tending-to-infinity-sequence-Preorder = pr2
```

## Properties

### The subtype of sequences tending to infinity is upward closed

Given two sequences `u ≤ v`, if `u` tends to infinity, so does `v`.

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  (u v : type-sequence-Preorder P) (I : leq-sequence-Preorder P u v)
  where

  modulus-leq-modulus-tends-to-infinity-sequence-Preorder :
    modulus-tends-to-infinity-sequence-Preorder P u →
    modulus-tends-to-infinity-sequence-Preorder P v
  modulus-leq-modulus-tends-to-infinity-sequence-Preorder =
    tot
      ( λ N Mu x n J →
        transitive-leq-Preorder P
          ( x)
          ( u n)
          ( v n)
          ( I n)
          ( Mu x n J))

  is-upward-closed-tends-to-infinity-sequence-Preorder :
    tends-to-infinity-sequence-Preorder P u →
    tends-to-infinity-sequence-Preorder P v
  is-upward-closed-tends-to-infinity-sequence-Preorder =
    map-is-inhabited modulus-leq-modulus-tends-to-infinity-sequence-Preorder
```
