# Wedges of types

```agda
module synthetic-homotopy-theory.wedges-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.unit-type
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-types
open import structured-types.pointed-maps
open import structured-types.pointed-cartesian-product-types

open import synthetic-homotopy-theory.cofibers
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

The **wedge** or **wedge sum** of two pointed types `a : A` and `b : B` is
defined by the following pushout.

```md
  unit ------> A
    |          |
    |          |
    v       ⌜  v
    B -----> A ∨* B
```

The wedge sum is canonically pointed at the (identified) images of `a` and `b`.

## Definition

```agda
_∨*_ :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Pointed-Type (l1 ⊔ l2)
pr1 (A ∨* B) =
  pushout
    ( const unit (pr1 A) (pr2 A))
    ( const unit (pr1 B) (pr2 B))
pr2 (A ∨* B) =
  inl-pushout
    ( const unit (pr1 A) (pr2 A))
    ( const unit (pr1 B) (pr2 B))
    ( pr2 A)

indexed-wedge :
  {l1 l2 : Level} (I : UU l1) (A : I → Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
pr1 (indexed-wedge I A) = cofiber (λ i → i , pt-Pointed-Type (A i))
pr2 (indexed-wedge I A) = pt-cofiber (λ i → i , pt-Pointed-Type (A i))
```

## Properties

### The canonical inclusion of the wedge sum into the pointed product

There is a canonical inclusion of the wedge sum into the pointed product that is
defined by the cogap map of the cocone defined by the canonical inclusions
`A → A ×* B ← B`.

```agda
map-prod-wedge-Pointed-Type :
  {l1 l2 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) →
  type-Pointed-Type (A ∨* B) → type-Pointed-Type (A ×* B)
map-prod-wedge-Pointed-Type (A , a) (B , b) =
  cogap
    ( λ _ → a)
    ( λ _ → b)
    ( (_, b) , (a ,_) , refl-htpy)

```
