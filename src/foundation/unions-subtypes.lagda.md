# Unions of subtypes

```agda
module foundation.unions-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-locale-of-subtypes
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.least-upper-bounds-large-posets
```

</details>

## Idea

The **union** of two [subtypes](foundation-core.subtypes.md) `A` and `B` is the
subtype that contains the elements that are in `A` or in `B`.

## Definition

### Unions of subtypes

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  union-subtype : subtype l1 X → subtype l2 X → subtype (l1 ⊔ l2) X
  union-subtype P Q x = (P x) ∨ (Q x)
```

### Unions of decidable subtypes

```agda
  union-decidable-subtype :
    decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  union-decidable-subtype P Q x = disjunction-Decidable-Prop (P x) (Q x)
```

### Unions of families of subtypes

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  where

  union-family-of-subtypes :
    {I : UU l2} (A : I → subtype l3 X) → subtype (l2 ⊔ l3) X
  union-family-of-subtypes = sup-powerset-Large-Locale

  is-least-upper-bound-union-family-of-subtypes :
    {I : UU l2} (A : I → subtype l3 X) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( powerset-Large-Poset X)
      ( A)
      ( union-family-of-subtypes A)
  is-least-upper-bound-union-family-of-subtypes =
    is-least-upper-bound-sup-powerset-Large-Locale
```

## Properties

### The union of families of subtypes preserves indexed inclusion

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {I : UU l2}
  (A : I → subtype l3 X) (B : I → subtype l4 X)
  where

  preserves-order-union-family-of-subtypes :
    ((i : I) → A i ⊆ B i) →
    union-family-of-subtypes A ⊆ union-family-of-subtypes B
  preserves-order-union-family-of-subtypes H x p =
    apply-universal-property-trunc-Prop p
      ( union-family-of-subtypes B x)
      ( λ (i , q) → unit-trunc-Prop (i , H i x q))
```

## TODO: Change title

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} (P : subtype l2 X) (Q : subtype l3 X)
  where

  subtype-union-left : P ⊆ union-subtype P Q
  subtype-union-left x = inl-disj-Prop (P x) (Q x)

  subtype-union-right : Q ⊆ union-subtype P Q
  subtype-union-right x = inr-disj-Prop (P x) (Q x)

  subtype-union-both :
    {l3 : Level} (S : subtype l3 X) → P ⊆ S → Q ⊆ S → union-subtype P Q ⊆ S
  subtype-union-both S P-sub-S Q-sub-S x =
    elim-disj-Prop (P x) (Q x) (S x) (P-sub-S x , Q-sub-S x)

module _
  {l1 l2 : Level} {X : UU l1} (P : subtype l2 X)
  where

  subtype-union-same : union-subtype P P ⊆ P
  subtype-union-same =
    subtype-union-both P P P (refl-leq-subtype P) (refl-leq-subtype P)

  eq-union-same : P ＝ union-subtype P P
  eq-union-same =
    antisymmetric-leq-subtype
    ( P)
    ( union-subtype P P)
    ( subtype-union-left P P)
    ( subtype-union-same)
```
