# Smash products of pointed types

```agda
module synthetic-homotopy-theory.smash-products-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.cofibers
open import synthetic-homotopy-theory.wedges-of-pointed-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Given two pointed types `a : A` and `b : B` we may form their **smash product**
as the following pushout

```md
 A ∨* B ----> A ×* B
    |           |
    |           |
    v        ⌜  v
  unit -----> A ∧* B
```

where the map `A ∨* B → A ×* B` is the canonical inclusion
`map-wedge-prod-Pointed-Type`.

Note that although the smash product is called a product, it is not a limit
construction. It is a quotient of the product, so it's a colimit.

## Definition

```agda
_∧*_ :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Pointed-Type (l1 ⊔ l2)
pr1 (A ∧* B) =
  pushout
    ( map-prod-wedge-Pointed-Type A B)
    ( λ _ → star)
pr2 (A ∧* B) = inr-pushout (map-prod-wedge-Pointed-Type A B) (λ _ → star) star
```
