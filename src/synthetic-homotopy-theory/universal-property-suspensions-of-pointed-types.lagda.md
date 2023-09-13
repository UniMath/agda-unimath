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

  pointed-map-unit-susp-loop-adj : X →∗ Ω (suspension-Pointed-Type X)
  pointed-map-unit-susp-loop-adj =
    pointed-map-loop-pointed-identity-suspension ∘∗
    pointed-map-concat-meridian-suspension

  map-unit-susp-loop-adj : type-Pointed-Type X →
    type-Ω (suspension-Pointed-Type X)
  map-unit-susp-loop-adj = map-pointed-map pointed-map-unit-susp-loop-adj

  map-counit-susp-loop-adj : (suspension (type-Ω X)) → type-Pointed-Type X
  map-counit-susp-loop-adj =
    map-inv-is-equiv
      ( up-suspension (type-Ω X) (type-Pointed-Type X))
      ( ( point-Pointed-Type X) ,
        ( point-Pointed-Type X) ,
        ( id))

  pointed-map-counit-susp-loop-adj :
    ( pair (suspension (type-Ω X)) north-suspension) →∗ X
  pr1 pointed-map-counit-susp-loop-adj = map-counit-susp-loop-adj
  pr2 pointed-map-counit-susp-loop-adj =
    up-suspension-north-suspension
      ( type-Ω X)
      ( type-Pointed-Type X)
      ( ( point-Pointed-Type X) ,
        ( point-Pointed-Type X) ,
        ( id))
```

#### The underlying map of the equivalence

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  map-equiv-susp-loop-adj :
    ((suspension-Pointed-Type X) →∗ Y) → (X →∗ Ω Y)
  map-equiv-susp-loop-adj f∗ =
    ((pointed-map-Ω f∗) ∘∗ (pointed-map-unit-susp-loop-adj X))
```

#### The underlying map of the inverse equivalence

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  map-inv-equiv-susp-loop-adj :
    (X →∗ Ω Y) → ((suspension-Pointed-Type X) →∗ Y)
  pr1 (map-inv-equiv-susp-loop-adj f∗) =
    map-inv-up-suspension
      ( type-Pointed-Type X)
      ( type-Pointed-Type Y)
      ( suspension-structure-map-into-Ω
        ( type-Pointed-Type X)
        ( Y)
        ( map-pointed-map f∗))
  pr2 (map-inv-equiv-susp-loop-adj f∗) =
    up-suspension-north-suspension
      ( type-Pointed-Type X)
      ( type-Pointed-Type Y)
      ( suspension-structure-map-into-Ω
      ( type-Pointed-Type X)
      ( Y)
      ( map-pointed-map f∗))
```

We now show these maps are inverses of each other.

#### The equivalence between pointed maps out of the suspension of X and pointed maps into the loop space of Y

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  equiv-susp-loop-adj : (suspension-Pointed-Type X →∗ Y) ≃ (X →∗ Ω Y)
  equiv-susp-loop-adj =
    ( left-unit-law-Σ-is-contr
      ( is-contr-total-path (point-Pointed-Type Y))
      ( (point-Pointed-Type Y) , refl)) ∘e
    ( ( inv-equiv
        ( associative-Σ
          ( type-Pointed-Type Y)
          ( λ z → (point-Pointed-Type Y) ＝ z)
          ( λ t →
            Σ ( type-Pointed-Type X →
                ( point-Pointed-Type Y) ＝ (pr1 t))
              ( λ f → f (point-Pointed-Type X) ＝ (pr2 t))))) ∘e
      ( ( equiv-tot (λ y1 → equiv-left-swap-Σ)) ∘e
        ( ( associative-Σ
            ( type-Pointed-Type Y)
            ( λ y1 →
              type-Pointed-Type X → point-Pointed-Type Y ＝ y1)
            ( λ z →
              Σ ( Id (point-Pointed-Type Y) (pr1 z))
                ( λ x → pr2 z (point-Pointed-Type X) ＝ x))) ∘e
          ( ( inv-equiv
            ( right-unit-law-Σ-is-contr
              ( λ ( z : Σ ( type-Pointed-Type Y)
                ( λ y1 →
                  type-Pointed-Type X →
                  point-Pointed-Type Y ＝ y1)) →
                    ( is-contr-total-path
                      ( (pr2 z) (point-Pointed-Type X)))))) ∘e
            ( ( left-unit-law-Σ-is-contr
                ( is-contr-total-path' (point-Pointed-Type Y))
                ( (point-Pointed-Type Y) , refl)) ∘e
              ( ( equiv-right-swap-Σ) ∘e
                ( equiv-Σ-equiv-base
                  ( λ c → (pr1 c) ＝ (point-Pointed-Type Y))
                  ( equiv-up-suspension
                    ( type-Pointed-Type X)
                    ( type-Pointed-Type Y)))))))))
```

#### The equivalence in the suspension-loop space adjunction is pointed

This remains to be shown.
[#702](https://github.com/UniMath/agda-unimath/issues/702)
