# Multivariable functoriality of set quotients

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module foundation.multivariable-functoriality-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.multivariable-operations
open import foundation.propositions
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.subtype-identity-principle

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Say we have a family of types `A1`, ..., `An` each equipped with an equivalence
relation `Ri`, as well as a type `X` equipped with an equivalence relation `X`,
Then, any multivariable operation from the `Ai`s to the `X` that respects the
equivalence relations extends uniquely to a multivariable operation from the
`Ai/Ri`s to `X/S`.

## Definition

### n-ary hom of equivalence relation

```agda
all-sim-Eq-Rel :
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  ( as : multivariable-input n As) →
  ( a's : multivariable-input n As) →
  UU l2
all-sim-Eq-Rel {l1} {l2} zero-ℕ As Rs as a's =
  raise-unit l2
all-sim-Eq-Rel {l1} {l2} (succ-ℕ n) As Rs as a's =
  sim-Eq-Rel (Rs (inr star))
    ( head-multivariable-input n As as)
    ( head-multivariable-input n As a's) ×
  all-sim-Eq-Rel n
    ( tail-functional-vec n As)
    ( λ i → Rs (inl-Fin n i))
    ( tail-multivariable-input n As as)
    ( tail-multivariable-input n As a's)

module _
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i))
  ( X : UU l1) (S : Eq-Rel l2 X)
  where

  preserves-sim-multivariable-map-Eq-Rel :
    multivariable-operation n As X →
    UU (l1 ⊔ l2)
  preserves-sim-multivariable-map-Eq-Rel f =
    ( as : multivariable-input n As) →
    ( a's : multivariable-input n As) →
    ( all-sim-Eq-Rel n As Rs as a's) →
    ( sim-Eq-Rel S
      ( f as)
      ( f a's))

  is-prop-preserves-sim-n-ary-map-Eq-Rel :
    (f : multivariable-operation n As X) →
    is-prop (preserves-sim-multivariable-map-Eq-Rel f)
  is-prop-preserves-sim-n-ary-map-Eq-Rel f =
    is-prop-Π
      ( λ as →
        ( is-prop-Π
          ( λ a's →
            ( is-prop-Π
              ( λ _ →
                ( is-prop-sim-Eq-Rel S
                  ( f as)
                  ( f a's)))))))

  preserves-sim-multivariable-map-Eq-Rel-Prop :
    multivariable-operation n As X →
    Prop (l1 ⊔ l2)
  preserves-sim-multivariable-map-Eq-Rel-Prop f =
    pair
      ( preserves-sim-multivariable-map-Eq-Rel f)
      ( is-prop-preserves-sim-n-ary-map-Eq-Rel f)

  multivariable-hom-Eq-Rel : UU (l1 ⊔ l2)
  multivariable-hom-Eq-Rel =
    type-subtype preserves-sim-multivariable-map-Eq-Rel-Prop

  map-multivariable-hom-Eq-Rel :
    multivariable-hom-Eq-Rel → multivariable-operation n As X
  map-multivariable-hom-Eq-Rel = pr1

  preserves-sim-multivariable-hom-Eq-Rel :
    ( f : multivariable-hom-Eq-Rel) →
    preserves-sim-multivariable-map-Eq-Rel
     ( map-multivariable-hom-Eq-Rel f)
  preserves-sim-multivariable-hom-Eq-Rel = pr2
```

## Properties

### Characterization of equality of `multivariable-hom-Eq-Rel`

```agda
  multivariable-htpy-hom-Eq-Rel :
    (f g : multivariable-hom-Eq-Rel) → UU l1
  multivariable-htpy-hom-Eq-Rel f g =
    ( map-multivariable-hom-Eq-Rel f) ~
      ( map-multivariable-hom-Eq-Rel g)

  refl-multivariable-htpy-hom-Eq-Rel :
    (f : multivariable-hom-Eq-Rel) → multivariable-htpy-hom-Eq-Rel f f
  refl-multivariable-htpy-hom-Eq-Rel f = refl-htpy

  multivariable-htpy-eq-hom-Eq-Rel :
    (f g : multivariable-hom-Eq-Rel) → (f ＝ g) →
    multivariable-htpy-hom-Eq-Rel f g
  multivariable-htpy-eq-hom-Eq-Rel f .f refl =
    refl-multivariable-htpy-hom-Eq-Rel f

  is-contr-total-multivariable-htpy-hom-Eq-Rel :
    (f : multivariable-hom-Eq-Rel) →
    is-contr (Σ multivariable-hom-Eq-Rel (multivariable-htpy-hom-Eq-Rel f))
  is-contr-total-multivariable-htpy-hom-Eq-Rel f =
    is-contr-total-Eq-subtype
      ( is-contr-total-htpy (map-multivariable-hom-Eq-Rel f))
      ( is-prop-preserves-sim-n-ary-map-Eq-Rel)
      ( map-multivariable-hom-Eq-Rel f)
      ( refl-multivariable-htpy-hom-Eq-Rel f)
      ( preserves-sim-multivariable-hom-Eq-Rel f)

  is-equiv-multivariable-htpy-eq-hom-Eq-Rel :
    (f g : multivariable-hom-Eq-Rel) →
      is-equiv (multivariable-htpy-eq-hom-Eq-Rel f g)
  is-equiv-multivariable-htpy-eq-hom-Eq-Rel f =
    fundamental-theorem-id
      ( is-contr-total-multivariable-htpy-hom-Eq-Rel f)
      ( multivariable-htpy-eq-hom-Eq-Rel f)

  extensionality-multivariable-hom-Eq-Rel :
    (f g : multivariable-hom-Eq-Rel) →
    (f ＝ g) ≃ multivariable-htpy-hom-Eq-Rel f g
  pr1 (extensionality-multivariable-hom-Eq-Rel f g) =
    multivariable-htpy-eq-hom-Eq-Rel f g
  pr2 (extensionality-multivariable-hom-Eq-Rel f g) =
    is-equiv-multivariable-htpy-eq-hom-Eq-Rel f g

  eq-multivariable-htpy-hom-Eq-Rel :
    (f g : multivariable-hom-Eq-Rel) →
    multivariable-htpy-hom-Eq-Rel f g → f ＝ g
  eq-multivariable-htpy-hom-Eq-Rel f g =
    map-inv-equiv (extensionality-multivariable-hom-Eq-Rel f g)
```
