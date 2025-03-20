# Intersections of subtypes

```agda
module foundation.intersections-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.large-locale-of-subtypes
open import foundation.powersets
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.propositions
open import foundation-core.subtypes

open import order-theory.greatest-lower-bounds-large-posets
```

</details>

## Idea

The intersection of two subtypes `A` and `B` is the subtype that contains the
elements that are in `A` and in `B`.

## Definition

### The intersection of two subtypes

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} (P : subtype l2 X) (Q : subtype l3 X)
  where

  intersection-subtype : subtype (l2 ⊔ l3) X
  intersection-subtype = meet-powerset-Large-Locale P Q

  is-greatest-binary-lower-bound-intersection-subtype :
    is-greatest-binary-lower-bound-Large-Poset
      ( powerset-Large-Poset X)
      ( P)
      ( Q)
      ( intersection-subtype)
  pr1
    ( pr1
      ( is-greatest-binary-lower-bound-intersection-subtype R)
      ( p , q) x r) =
    p x r
  pr2
    ( pr1
      ( is-greatest-binary-lower-bound-intersection-subtype R)
      ( p , q) x r) = q x r
  pr1 (pr2 (is-greatest-binary-lower-bound-intersection-subtype R) p) x r =
    pr1 (p x r)
  pr2 (pr2 (is-greatest-binary-lower-bound-intersection-subtype R) p) x r =
    pr2 (p x r)
```

### The intersection of two decidable subtypes

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  intersection-decidable-subtype :
    decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  intersection-decidable-subtype P Q x = conjunction-Decidable-Prop (P x) (Q x)
```

### The intersection of a family of subtypes

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  where

  intersection-family-of-subtypes :
    {I : UU l2} (P : I → subtype l3 X) → subtype (l2 ⊔ l3) X
  intersection-family-of-subtypes {I} P x = Π-Prop I (λ i → P i x)
```
