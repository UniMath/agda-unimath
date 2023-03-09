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
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.24-pushouts
open import synthetic-homotopy-theory.cocones-pushouts
open import synthetic-homotopy-theory.cofibers
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

```agda
_∨_ :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
A ∨ B =
  pair
    ( pushout
      ( const unit (pr1 A) (pr2 A))
      ( const unit (pr1 B) (pr2 B)))
    ( inl-pushout
      ( const unit (pr1 A) (pr2 A))
      ( const unit (pr1 B) (pr2 B))
      ( pr2 A))

indexed-wedge :
  {l1 l2 : Level} (I : UU l1) (A : I → Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
indexed-wedge I A =
  pair
    ( cofiber (λ i → pair i (pr2 (A i))))
    ( pt-cofiber (λ i → pair i (pr2 (A i))))

wedge-inclusion :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  pr1 (A ∨ B) → (pr1 A) × (pr1 B)
wedge-inclusion {l1} {l2} (pair A a) (pair B b) =
  map-inv-is-equiv
    ( up-pushout
      ( const unit A a)
      ( const unit B b)
      ( A × B))
    ( pair
      ( λ x → pair x b)
      ( pair
        ( λ y → pair a y)
        ( refl-htpy)))
```
