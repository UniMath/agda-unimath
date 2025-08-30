# Cartesian products of subtypes

```agda
module foundation.cartesian-products-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given types `A` and `B` and subtypes `S ⊆ A` and `T ⊆ B`, a pair
`(a , b) : A × B` is in the
{{#concept "Cartesian product" disambiguation="of subtypes" WDID=Q173740 WD="Cartesian product" Agda=product-subtype}}
of `S` and `T` if `a ∈ S` and `b ∈ T`.

## Definition

```agda
product-subtype :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  subtype l3 A → subtype l4 B → subtype (l3 ⊔ l4) (A × B)
product-subtype P Q (a , b) = P a ∧ Q b
```
