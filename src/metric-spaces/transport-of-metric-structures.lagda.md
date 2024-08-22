# Transport of metric structures

```agda
module metric-spaces.transport-of-metric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.neighbourhood-relations
```

</details>

## Idea

Any [metric structure](metric-spaces.metric-structures.md) on a type equal can
be transported on any equal type. This defines the
{{#concept "transport of metric structure" Agda=tr-Metric-Structure}}.

## Definitions

### Transporting metric structures

```agda
module _
  {l1 l2 : Level}
  where

  tr-Metric-Structure :
    (A B : UU l1) →
    (A ＝ B) →
    Metric-Structure l2 A →
    Metric-Structure l2 B
  tr-Metric-Structure A B = tr (Metric-Structure l2)

  compute-neighbourhood-tr-Metric-Structure :
    (A B : UU l1) (H : A ＝ B) (S : Metric-Structure l2 A) →
    (d : ℚ⁺) (x y : A) →
    Id
      ( neighbourhood-Metric-Structure A S d x y)
      ( neighbourhood-Metric-Structure
        ( B)
        ( tr-Metric-Structure A B H S)
        ( d)
        ( map-eq H x)
        ( map-eq H y))
  compute-neighbourhood-tr-Metric-Structure A .A refl S d x y = refl
```

## Properties

### Two structures between equal types are transported if and only if the cannonical equality map is an isometry

```agda
module _
  {l : Level} (A B : UU l) (e : A ＝ B)
  (U : Metric-Structure l A)
  (V : Metric-Structure l B)
  where

  equiv-is-isometry-map-eq-Eq-tr-Metric-Structure :
    Eq-Metric-Structure
      ( B)
      ( tr-Metric-Structure A B e U)
      ( V) ≃
    is-isometry-function-Metric-Space (A , U) (B , V) (map-eq e)
  equiv-is-isometry-map-eq-Eq-tr-Metric-Structure =
    equiv-iff
      ( Eq-prop-Metric-Structure
        ( B)
        ( tr-Metric-Structure A B e U)
        ( V))
      ( is-isometry-prop-function-Metric-Space (A , U) (B , V) (map-eq e))
      ( forward)
      ( backward)
    where

    forward :
      Eq-Metric-Structure
        ( B)
        ( tr-Metric-Structure A B e U)
        ( V) →
      is-isometry-function-Metric-Space (A , U) (B , V) (map-eq e)
    forward H d x y =
      H d (map-eq e x) (map-eq e y) ∘iff
      iff-eq (compute-neighbourhood-tr-Metric-Structure A B e U d x y)

    backward :
      is-isometry-function-Metric-Space (A , U) (B , V) (map-eq e) →
      Eq-Metric-Structure
        ( B)
        ( tr-Metric-Structure A B e U)
        ( V)
    backward I d x y =
      logical-equivalence-reasoning
        ( is-in-neighbourhood-Metric-Structure
          ( B)
          ( tr-Metric-Structure A B e U)
          ( d)
          ( x)
          ( y))
        ↔ ( is-in-neighbourhood-Metric-Structure
            ( B)
            ( tr-Metric-Structure A B e U)
            ( d)
            ( map-eq e (map-inv-equiv (equiv-eq e) x))
            ( map-eq e (map-inv-equiv (equiv-eq e) y)))
          by
            binary-tr
              ( λ u v →
                ( is-in-neighbourhood-Metric-Structure
                  ( B)
                  ( tr-Metric-Structure A B e U)
                  ( d)
                  ( x)
                  ( y)) ↔
                ( is-in-neighbourhood-Metric-Structure
                  ( B)
                  ( tr-Metric-Structure A B e U)
                  ( d)
                  ( u)
                  ( v)))
              ( inv (is-section-map-inv-equiv (equiv-eq e) x))
              ( inv (is-section-map-inv-equiv (equiv-eq e) y))
              ( id-iff)
        ↔ ( is-in-neighbourhood-Metric-Structure
            ( A)
            ( U)
            ( d)
            ( map-inv-equiv (equiv-eq e) x)
            ( map-inv-equiv (equiv-eq e) y))
          by
            iff-eq
              ( inv
                ( compute-neighbourhood-tr-Metric-Structure
                  ( A)
                  ( B)
                  ( e)
                  ( U)
                  ( d)
                  ( map-inv-equiv (equiv-eq e) x)
                  ( map-inv-equiv (equiv-eq e) y)))
        ↔ ( is-in-neighbourhood-Metric-Structure
            ( B)
            ( V)
            ( d)
            ( map-eq e (map-inv-equiv (equiv-eq e) x))
            ( map-eq e (map-inv-equiv (equiv-eq e) y)))
          by I d (map-inv-equiv (equiv-eq e) x) (map-inv-equiv (equiv-eq e) y)
        ↔ (is-in-neighbourhood-Metric-Structure B V d x y)
          by
            binary-tr
              ( λ u v →
                ( is-in-neighbourhood-Metric-Structure B V d u v) ↔
                ( is-in-neighbourhood-Metric-Structure B V d x y))
              ( inv (is-section-map-inv-equiv (equiv-eq e) x))
              ( inv (is-section-map-inv-equiv (equiv-eq e) y))
              ( id-iff)
```
