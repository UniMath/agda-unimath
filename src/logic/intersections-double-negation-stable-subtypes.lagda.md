# Intersections of double negation stable subtypes

```agda
module logic.intersections-double-negation-stable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.intersections-subtypes
open import foundation.subtypes
open import foundation.universe-levels

open import logic.double-negation-elimination
open import logic.double-negation-stable-subtypes
```

</details>

## Idea

Given two
[double negation stable subtypes](logic.double-negation-stable-subtypes.md) `P`
and `Q` of a common carrier type `A`, then their
[intersection](foundation.intersections-subtypes.md) is again double negation
stable.

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : subtype l2 A) (Q : subtype l3 A)
  where

  is-double-negation-stable-intersection-subtype :
    is-double-negation-stable-subtype P →
    is-double-negation-stable-subtype Q →
    is-double-negation-stable-subtype (intersection-subtype P Q)
  is-double-negation-stable-intersection-subtype p q x =
    double-negation-elim-product (p x) (q x)

module _
  {l1 l2 l3 : Level} {A : UU l1}
  (P : double-negation-stable-subtype l2 A)
  (Q : double-negation-stable-subtype l3 A)
  where

  intersection-double-negation-stable-subtype :
    double-negation-stable-subtype (l2 ⊔ l3) A
  intersection-double-negation-stable-subtype =
    make-double-negation-stable-subtype
    ( intersection-subtype
      ( subtype-double-negation-stable-subtype P)
      ( subtype-double-negation-stable-subtype Q))
    ( is-double-negation-stable-intersection-subtype
      ( subtype-double-negation-stable-subtype P)
      ( subtype-double-negation-stable-subtype Q)
      ( is-double-negation-stable-double-negation-stable-subtype P)
      ( is-double-negation-stable-double-negation-stable-subtype Q))
```
