# Universal Property of suspensions of pointed types

```agda
module synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.suspensions-of-pointed-types
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

The [suspension](synthetic-homotopy-theory.suspensions-of-types.md) of a
[pointed type](structured-types.pointed-types.md) enjoys an additional universal
property, on top of
[the universal property associtated with being a suspension](synthetic-homotopy-theory.universal-property-suspensions.md).
This universal property is packaged in an adjunction: the suspension
construction on pointed types is left adjoint to the loop space construction.

#### The unit and counit of the adjunction

```agda
module _
  {l1 : Level} (X : Pointed-Type l1)
  where

  pointed-equiv-loop-pointed-identity-suspension :
    ( pair
      ( north-suspension ＝ south-suspension)
      ( meridian-suspension (point-Pointed-Type X))) ≃∗
    ( Ω (suspension-Pointed-Type X))
  pointed-equiv-loop-pointed-identity-suspension =
    pointed-equiv-loop-pointed-identity
      ( suspension-Pointed-Type X)
      ( meridian-suspension (point-Pointed-Type X))

  pointed-map-loop-pointed-identity-suspension :
    ( pair
      ( north-suspension ＝ south-suspension)
      ( meridian-suspension (point-Pointed-Type X))) →∗
    Ω (suspension-Pointed-Type X)
  pointed-map-loop-pointed-identity-suspension =
    pointed-map-pointed-equiv
      ( pointed-equiv-loop-pointed-identity-suspension)

  pointed-map-concat-meridian-suspension :
    X →∗
    ( pair
      ( north-suspension ＝ south-suspension)
      ( meridian-suspension (point-Pointed-Type X)))
  pr1 pointed-map-concat-meridian-suspension = meridian-suspension
  pr2 pointed-map-concat-meridian-suspension = refl

  pointed-map-unit-suspension-loop-adjunction :
    X →∗ Ω (suspension-Pointed-Type X)
  pointed-map-unit-suspension-loop-adjunction =
    pointed-map-loop-pointed-identity-suspension ∘∗
    pointed-map-concat-meridian-suspension

  map-unit-suspension-loop-adjunction :
    type-Pointed-Type X → type-Ω (suspension-Pointed-Type X)
  map-unit-suspension-loop-adjunction =
    map-pointed-map pointed-map-unit-suspension-loop-adjunction

  map-counit-suspension-loop-adjunction :
    suspension (type-Ω X) → type-Pointed-Type X
  map-counit-suspension-loop-adjunction =
    map-inv-is-equiv
      ( up-suspension (type-Pointed-Type X))
      ( point-Pointed-Type X , point-Pointed-Type X , id)

  pointed-map-counit-suspension-loop-adjunction :
    pair (suspension (type-Ω X)) (north-suspension) →∗ X
  pr1 pointed-map-counit-suspension-loop-adjunction =
    map-counit-suspension-loop-adjunction
  pr2 pointed-map-counit-suspension-loop-adjunction =
    compute-north-cogap-suspension
      ( point-Pointed-Type X , point-Pointed-Type X , id)
```

#### The transposing maps of the adjunction

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  transpose-suspension-loop-adjunction :
    (suspension-Pointed-Type X →∗ Y) → (X →∗ Ω Y)
  transpose-suspension-loop-adjunction f∗ =
    pointed-map-Ω f∗ ∘∗ pointed-map-unit-suspension-loop-adjunction X

module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  inv-transpose-suspension-loop-adjunction :
    (X →∗ Ω Y) → (suspension-Pointed-Type X →∗ Y)
  pr1 (inv-transpose-suspension-loop-adjunction f∗) =
    cogap-suspension
      ( suspension-structure-map-into-Ω
        ( type-Pointed-Type X)
        ( Y)
        ( map-pointed-map f∗))
  pr2 (inv-transpose-suspension-loop-adjunction f∗) =
    compute-north-cogap-suspension
      ( suspension-structure-map-into-Ω
        ( type-Pointed-Type X)
        ( Y)
        ( map-pointed-map f∗))
```

We now show these maps are inverses of each other.

#### The transposing equivalence between pointed maps out of the suspension of `X` and pointed maps into the loop space of `Y`

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  equiv-transpose-suspension-loop-adjunction :
    (suspension-Pointed-Type X →∗ Y) ≃ (X →∗ Ω Y)
  equiv-transpose-suspension-loop-adjunction =
    ( left-unit-law-Σ-is-contr
      ( is-torsorial-Id (point-Pointed-Type Y))
      ( point-Pointed-Type Y , refl)) ∘e
    ( inv-associative-Σ) ∘e
    ( equiv-tot (λ y1 → equiv-left-swap-Σ)) ∘e
    ( associative-Σ) ∘e
    ( inv-right-unit-law-Σ-is-contr
      ( λ z → is-torsorial-Id (pr2 z (point-Pointed-Type X)))) ∘e
    ( left-unit-law-Σ-is-contr
      ( is-torsorial-Id' (point-Pointed-Type Y))
      ( point-Pointed-Type Y , refl)) ∘e
    ( equiv-right-swap-Σ) ∘e
    ( equiv-Σ-equiv-base
      ( λ c → pr1 c ＝ point-Pointed-Type Y)
      ( equiv-up-suspension))
```

#### The equivalence in the suspension-loop space adjunction is pointed

This remains to be shown.
[#702](https://github.com/UniMath/agda-unimath/issues/702)
