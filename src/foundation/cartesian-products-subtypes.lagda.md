# Cartesian products of subtypes

```agda
module foundation.cartesian-products-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
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

type-product-subtype :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  subtype l3 A → subtype l4 B → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
type-product-subtype P Q = type-subtype (product-subtype P Q)
```

## Properties

### The type of the Cartesian product of subtypes is equivalent to the Cartesian products of their types

```agda
equiv-product-subtype :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  (S : subtype l3 A) (T : subtype l4 B) →
  type-product-subtype S T ≃ (type-subtype S × type-subtype T)
equiv-product-subtype S T =
  ( (λ ((s , t) , s∈S , t∈T) → ((s , s∈S) , (t , t∈T))) ,
    is-equiv-is-invertible
      ( λ ((s , s∈S) , (t , t∈T)) → ((s , t) , s∈S , t∈T))
      ( λ _ → refl)
      ( λ _ → refl))
```
