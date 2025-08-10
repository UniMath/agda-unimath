# Disjoint subtypes

```agda
module foundation.disjoint-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-subtypes
open import foundation.empty-types
open import foundation.intersections-subtypes
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Two [subtypes](foundation-core.subtypes.md) are
{{#concept "disjoint" WDID=Q215382 WD="disjoint sets" Agda=disjoint-subtype}} if
their [intersection](foundation.intersections-subtypes.md) is
[empty](foundation.empty-subtypes.md).

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (B : subtype l2 A) (C : subtype l3 A)
  where

  disjoint-subtype-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  disjoint-subtype-Prop = is-empty-prop-subtype (intersection-subtype B C)

  disjoint-subtype : UU (l1 ⊔ l2 ⊔ l3)
  disjoint-subtype = type-Prop disjoint-subtype-Prop
```

## Properties

### A subtype disjoint from itself is empty

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : subtype l2 A)
  where

  is-empty-disjoint-subtype-self :
    disjoint-subtype B B → is-empty (type-subtype B)
  is-empty-disjoint-subtype-self H (b , b∈B) = H b (b∈B , b∈B)
```
