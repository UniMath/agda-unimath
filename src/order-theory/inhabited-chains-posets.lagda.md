# Inhabited chains in posets

```agda
module order-theory.inhabited-chains-posets where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.directed-families-posets

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.chains-posets
open import order-theory.posets
open import order-theory.subposets
open import order-theory.total-preorders
```

</details>

## Idea

An
{{#concept "inhabited chain" Disambiguation="in a poset" Agda=inhabited-chain-Poset}}
in a [poset](order-theory.posets.md) `P` is a
[subtype](foundation-core.subtypes.md) `S` of `P` such that the ordering of `P`
restricted to `S` is [linear](order-theory.total-orders.md) and
[inhabited](foundation.inhabited-types.md).

## Definitions

### The predicate on chains in posets of being inhabited

```agda
module _
  {l1 l2 l3 : Level} (X : Poset l1 l2) (S : chain-Poset l3 X)
  where

  is-inhabited-prop-chain-Poset : Prop (l1 ⊔ l3)
  is-inhabited-prop-chain-Poset =
    is-inhabited-subtype-Prop (subposet-chain-Poset X S)

  is-inhabited-chain-Poset : UU (l1 ⊔ l3)
  is-inhabited-chain-Poset =
    type-Prop is-inhabited-prop-chain-Poset

  is-prop-is-inhabited-chain-Poset :
    is-prop is-inhabited-chain-Poset
  is-prop-is-inhabited-chain-Poset =
    is-prop-type-Prop is-inhabited-prop-chain-Poset
```

### Inhabited chains in posets

```agda
inhabited-chain-Poset :
  {l1 l2 : Level} (l : Level) (X : Poset l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l)
inhabited-chain-Poset l X =
  Σ (chain-Poset l X) (is-inhabited-chain-Poset X)

module _
  {l1 l2 l3 : Level} (X : Poset l1 l2) (C : inhabited-chain-Poset l3 X)
  where

  chain-inhabited-chain-Poset : chain-Poset l3 X
  chain-inhabited-chain-Poset = pr1 C

  subposet-inhabited-chain-Poset : Subposet l3 X
  subposet-inhabited-chain-Poset =
    subposet-chain-Poset X chain-inhabited-chain-Poset

  is-chain-inhabited-chain-Poset :
    is-chain-Subposet X subposet-inhabited-chain-Poset
  is-chain-inhabited-chain-Poset =
    is-chain-subposet-chain-Poset X chain-inhabited-chain-Poset

  is-inhabited-inhabited-chain-Poset :
    is-inhabited-chain-Poset X chain-inhabited-chain-Poset
  is-inhabited-inhabited-chain-Poset = pr2 C

  type-inhabited-chain-Poset : UU (l1 ⊔ l3)
  type-inhabited-chain-Poset =
    type-subtype subposet-inhabited-chain-Poset

  inclusion-subposet-inhabited-chain-Poset :
    type-inhabited-chain-Poset → type-Poset X
  inclusion-subposet-inhabited-chain-Poset =
    inclusion-subtype subposet-inhabited-chain-Poset

module _
  {l1 l2 l3 l4 : Level} (X : Poset l1 l2)
  (C : inhabited-chain-Poset l3 X) (D : inhabited-chain-Poset l4 X)
  where

  inclusion-prop-inhabited-chain-Poset : Prop (l1 ⊔ l3 ⊔ l4)
  inclusion-prop-inhabited-chain-Poset =
    inclusion-prop-chain-Poset X
      ( chain-inhabited-chain-Poset X C)
      ( chain-inhabited-chain-Poset X D)

  inclusion-inhabited-chain-Poset : UU (l1 ⊔ l3 ⊔ l4)
  inclusion-inhabited-chain-Poset =
    type-Prop inclusion-prop-inhabited-chain-Poset

  is-prop-inclusion-inhabited-chain-Poset :
    is-prop inclusion-inhabited-chain-Poset
  is-prop-inclusion-inhabited-chain-Poset =
    is-prop-type-Prop inclusion-prop-inhabited-chain-Poset
```

## Properties

### Inhabited chains are directed families

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) (x : inhabited-chain-Poset l3 P)
  where

  type-directed-family-inhabited-chain-Poset : UU (l1 ⊔ l3)
  type-directed-family-inhabited-chain-Poset = type-inhabited-chain-Poset P x

  is-inhabited-type-directed-family-inhabited-chain-Poset :
    is-inhabited type-directed-family-inhabited-chain-Poset
  is-inhabited-type-directed-family-inhabited-chain-Poset =
    is-inhabited-inhabited-chain-Poset P x

  inhabited-type-directed-family-inhabited-chain-Poset :
    Inhabited-Type (l1 ⊔ l3)
  inhabited-type-directed-family-inhabited-chain-Poset =
    type-directed-family-inhabited-chain-Poset ,
    is-inhabited-type-directed-family-inhabited-chain-Poset

  family-directed-family-inhabited-chain-Poset :
    type-directed-family-inhabited-chain-Poset → type-Poset P
  family-directed-family-inhabited-chain-Poset =
    inclusion-subposet-inhabited-chain-Poset P x

  is-directed-family-directed-family-inhabited-chain-Poset :
    is-directed-family-Poset P
      inhabited-type-directed-family-inhabited-chain-Poset
      family-directed-family-inhabited-chain-Poset
  is-directed-family-directed-family-inhabited-chain-Poset u v =
    elim-disjunction
      ( ∃ ( type-directed-family-inhabited-chain-Poset)
          ( λ k →
            leq-prop-Poset P
              ( family-directed-family-inhabited-chain-Poset u)
              ( family-directed-family-inhabited-chain-Poset k) ∧
            leq-prop-Poset P
              ( family-directed-family-inhabited-chain-Poset v)
              ( family-directed-family-inhabited-chain-Poset k)))
      ( λ p → intro-exists v (p , refl-leq-Poset P (pr1 v)))
      ( λ p → intro-exists u (refl-leq-Poset P (pr1 u) , p))
      ( is-chain-inhabited-chain-Poset P x u v)

  directed-family-inhabited-chain-Poset :
    directed-family-Poset (l1 ⊔ l3) P
  directed-family-inhabited-chain-Poset =
    inhabited-type-directed-family-inhabited-chain-Poset ,
    family-directed-family-inhabited-chain-Poset ,
    is-directed-family-directed-family-inhabited-chain-Poset
```
