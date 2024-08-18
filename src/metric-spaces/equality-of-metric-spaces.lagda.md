# Equality of metric spaces

```agda
module metric-spaces.equality-of-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.neighbourhood-relations
open import metric-spaces.transport-of-metric-structures
```

</details>

## Idea

Two [metric-spaces](metric-spaces.metric-spaces.md) with equal carrier types are
equal if the natural induced map between the carrier types is an
[isometry](metric-spaces.isometry-metric-spaces.md).

## Definitions

### Equality of metric spaces

```agda
module _
  {l : Level} (A B : Metric-Space l)
  (e : type-Metric-Space A ＝ type-Metric-Space B)
  where

  lemma-isometry-Metric-Space :
    is-isometry-function-Metric-Space A B (map-eq e) →
    is-isometry-function-Metric-Space
      ( tr-Metric-Space A (type-Metric-Space B) e)
      ( B)
      ( id)
  lemma-isometry-Metric-Space H d x y =
    logical-equivalence-reasoning
      ( is-in-neighbourhood-Metric-Space
        ( tr-Metric-Space A (type-Metric-Space B) e)
        ( d)
        ( x)
        ( y))
      ↔ ( is-in-neighbourhood-Metric-Space
          ( A)
          ( d)
          ( map-inv-equiv (equiv-eq e) x)
          ( map-inv-equiv (equiv-eq e) y))
        by
          is-isometry-map-isometry-function-Metric-Space
            ( tr-Metric-Space A (type-Metric-Space B) e)
            ( A)
            ( inv-isometry-tr-Metric-Space A (type-Metric-Space B) e)
            ( d)
            ( x)
            ( y)
      ↔ ( is-in-neighbourhood-Metric-Space
          ( B)
          ( d)
          ( map-eq e (map-inv-equiv (equiv-eq e) x))
          ( map-eq e (map-inv-equiv (equiv-eq e) y)))
        by
          H
            ( d)
            ( map-inv-equiv (equiv-eq e) x)
            ( map-inv-equiv (equiv-eq e) y)
      ↔ ( is-in-neighbourhood-Metric-Space B d x y)
        by
          binary-tr
            ( λ u v →
              ( is-in-neighbourhood-Metric-Space B d u v) ↔
              ( is-in-neighbourhood-Metric-Space B d x y))
            ( inv (is-section-map-inv-equiv (equiv-eq e) x))
            ( inv (is-section-map-inv-equiv (equiv-eq e) y))
            ( id-iff)

  eq-Metric-Space :
    is-isometry-function-Metric-Space A B (map-eq e) → A ＝ B
  eq-Metric-Space H =
    eq-pair-Σ
      ( e)
      ( eq-type-subtype
        ( is-metric-prop-neighbourhood (type-Metric-Space B))
        ( eq-neighbourhood-Relation
          ( type-Metric-Space B)
          ( neighbourhood-Metric-Space
            ( tr-Metric-Space A (type-Metric-Space B) e))
          ( neighbourhood-Metric-Space B)
          ( lemma-isometry-Metric-Space H)))
```

## Properties

### Isometrically equivalent metric spaces are equal

```agda
lemma-eq-type :
  {l : Level} (X Y : UU l) (E : X ＝ Y) (x : X) →
  map-equiv (equiv-eq E) x ＝ map-eq E x
lemma-eq-type X .X refl x = refl
```

```agda
module _
  {l : Level} (A B : Metric-Space l)
  (e : type-Metric-Space A ≃ type-Metric-Space B)
  (I : is-isometry-function-Metric-Space A B (map-equiv e))
  where

  eq-isometric-equiv-Metric-Space : A ＝ B
  eq-isometric-equiv-Metric-Space =
    eq-Metric-Space
      ( A)
      ( B)
      ( eq-equiv e)
      ( tr
        ( is-isometry-function-Metric-Space A B)
        ( eq-htpy
          ( λ x →
            ap
              ( λ H → map-equiv H x)
              ( inv (is-section-eq-equiv e)) ∙
            ( lemma-eq-type
              ( type-Metric-Space A)
              ( type-Metric-Space B)
              ( eq-equiv e)
              ( x))))
        ( I))
```

```agda
module _
  {l : Level} (A B : Metric-Space l)
  (f : function-carrier-type-Metric-Space A B)
  (e : is-equiv f)
  (I : is-isometry-function-Metric-Space A B f)
  where

  eq-isometric-is-equiv-Metric-Space : A ＝ B
  eq-isometric-is-equiv-Metric-Space =
    eq-isometric-equiv-Metric-Space A B (f , e) I
```

### Transporting metric structures is the identity in the type of metric spaces

```agda
module _
  {l : Level} (A : Metric-Space l) (B : UU l) (e : type-Metric-Space A ＝ B)
  where

  eq-tr-Metric-Space : A ＝ tr-Metric-Space A B e
  eq-tr-Metric-Space =
    eq-isometric-is-equiv-Metric-Space
      ( A)
      ( tr-Metric-Space A B e)
      ( map-eq e)
      ( is-equiv-map-equiv (equiv-eq e))
      ( is-isometry-map-eq-tr-Metric-Space A B e)
```
