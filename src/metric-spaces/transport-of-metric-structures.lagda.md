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
open import metric-spaces.neighbourhood-relations
```

</details>

## Idea

Any type equal to the carrier type of a
[metric space](metric-spaces.metric-spaces.md) inherits a metric structure.
Moreover, the
{{#concept "transport" Disambiguation="of metric space" Agda=tr-Metric-Space}}
of metric spaces produces a metric space
[isometric](metric-spaces.isometry-metric-spaces.md) to the initial one.

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

### Transport of metric spaces

```agda
module _
  {l : Level} (A : Metric-Space l) (B : UU l)
  (H : type-Metric-Space A ＝ B)
  where

  tr-Metric-Space : Metric-Space l
  tr-Metric-Space =
    B ,
    tr-Metric-Structure
      ( type-Metric-Space A)
      ( B)
      ( H)
      ( structure-Metric-Space A)

  compute-neighbourhood-tr-Metric-Space :
    (d : ℚ⁺) (x y : type-Metric-Space A) →
    (neighbourhood-Metric-Space A d x y) ＝
    (neighbourhood-Metric-Space tr-Metric-Space d (map-eq H x) (map-eq H y))
  compute-neighbourhood-tr-Metric-Space =
    compute-neighbourhood-tr-Metric-Structure
      ( type-Metric-Space A)
      ( B)
      ( H)
      ( structure-Metric-Space A)
```

## Properties

### Transport along refl is the identity

```agda
module _
  {l : Level} (A : Metric-Space l)
  where

  compute-tr-refl-Metric-Space :
    tr-Metric-Space A (type-Metric-Space A) refl ＝ A
  compute-tr-refl-Metric-Space = refl
```

### The transport of metric structures is an isometry

```agda
module _
  {l : Level} (A : Metric-Space l) (B : UU l)
  (e : type-Metric-Space A ＝ B)
  where

  is-isometry-map-eq-tr-Metric-Space :
    is-isometry-function-Metric-Space A (tr-Metric-Space A B e) (map-eq e)
  is-isometry-map-eq-tr-Metric-Space d x y =
    iff-eq (compute-neighbourhood-tr-Metric-Space A B e d x y)

  isometry-tr-Metric-Space :
    isometry-function-Metric-Space A (tr-Metric-Space A B e)
  isometry-tr-Metric-Space = map-eq e , is-isometry-map-eq-tr-Metric-Space

  inv-isometry-tr-Metric-Space :
    isometry-function-Metric-Space (tr-Metric-Space A B e) A
  inv-isometry-tr-Metric-Space =
    map-inv-equiv (equiv-eq e) ,
    is-isometry-map-inv-is-equiv-Metric-Space
      ( A)
      ( tr-Metric-Space A B e)
      ( map-eq e)
      ( is-isometry-map-eq-tr-Metric-Space)
      ( is-equiv-map-equiv (equiv-eq e))
```
