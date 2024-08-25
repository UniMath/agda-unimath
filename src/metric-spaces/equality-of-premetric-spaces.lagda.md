# Equality of premetric spaces

```agda
module metric-spaces.equality-of-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.isometry-premetric-spaces
open import metric-spaces.premetric-spaces
open import metric-spaces.premetric-structures
```

</details>

## Idea

By the
[identity principle of depdendent pair types](foundation.equality-dependent-pair-types.md),
equality of two [premetric spaces](metric-spaces.premetric-spaces.md) is
equivalent to equality of their carrier type with a proof that this equality
transports the [premetric structures](metric-spaces.premetric-structures.md).

This last condition holds if and only if the
[natural map induced by the equality](foundation.univalence.md) of their carrier
types is an [isometry](metric-spaces.isometry-premetric-spaces.md).

It follows that
{{#concept "isometric equality" Disambiguation="of premetric spaces" Agda=isometric-eq-Premetric-Space}}
characterizes equality of premetric spaces.

## Definitions

### Two premetric spaces are equal if their carrier types are equal and their premetric structures transported

```agda
module _
  {l1 l2 : Level} (A B : Premetric-Space l1 l2)
  where

  equiv-eq-tr-Premetric-Space :
    (A ＝ B) ≃
    Σ ( type-Premetric-Space A ＝ type-Premetric-Space B)
      ( λ e →
        tr (Premetric l2) e (structure-Premetric-Space A) ＝
        structure-Premetric-Space B)
  equiv-eq-tr-Premetric-Space = equiv-pair-eq-Σ A B
```

### The property of being an isometric equality between carrier types of premetric spaces

```agda
module _
  {l1 l2 l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1 l2')
  where

  is-isometric-eq-prop-Premetric-Space :
    (type-Premetric-Space A ＝ type-Premetric-Space B) → Prop (l1 ⊔ l2 ⊔ l2')
  is-isometric-eq-prop-Premetric-Space e =
    is-isometry-prop-Premetric-Space A B (map-eq e)

  is-isometric-eq-Premetric-Space :
    (type-Premetric-Space A ＝ type-Premetric-Space B) → UU (l1 ⊔ l2 ⊔ l2')
  is-isometric-eq-Premetric-Space e =
    type-Prop (is-isometric-eq-prop-Premetric-Space e)

  is-prop-is-isometric-eq-Premetric-Space :
    (e : type-Premetric-Space A ＝ type-Premetric-Space B) →
    is-prop (is-isometric-eq-Premetric-Space e)
  is-prop-is-isometric-eq-Premetric-Space e =
    is-prop-type-Prop (is-isometric-eq-prop-Premetric-Space e)

  isometric-eq-Premetric-Space : UU (lsuc l1 ⊔ l2 ⊔ l2')
  isometric-eq-Premetric-Space =
    type-subtype is-isometric-eq-prop-Premetric-Space
```

## Properties

### An equality between carrier types of premmetric spaces transport the metric structures if and only if is it isometric

```agda
module _
  {l1 l2 : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1 l2)
  (e : type-Premetric-Space A ＝ type-Premetric-Space B)
  where

  equiv-is-isometry-map-eq-tr-Premetric-Space :
    Id
      ( tr (Premetric l2) e (structure-Premetric-Space A))
      ( structure-Premetric-Space B) ≃
    is-isometry-Premetric-Space A B (map-eq e)
  equiv-is-isometry-map-eq-tr-Premetric-Space =
    ( equiv-iff
      ( Eq-prop-Premetric
        ( tr (Premetric l2) e (structure-Premetric-Space A))
        ( structure-Premetric-Space B))
      ( is-isometry-prop-Premetric-Space A B (map-eq e))
      ( forward)
      ( backward)) ∘e
    ( equiv-Eq-eq-Premetric
      ( tr (Premetric l2) e (structure-Premetric-Space A))
      ( structure-Premetric-Space B))
    where

    forward :
      Eq-Premetric
        ( tr (Premetric l2) e (structure-Premetric-Space A))
        ( structure-Premetric-Space B) →
      is-isometry-Premetric-Space A B (map-eq e)
    forward H d x y =
      H d (map-eq e x) (map-eq e y) ∘iff
      eq-map-eq-tr-Premetric
        ( type-Premetric-Space A)
        ( type-Premetric-Space B)
        ( e)
        ( structure-Premetric-Space A)
        ( d)
        ( x)
        ( y)

    backward :
      is-isometry-Premetric-Space A B (map-eq e) →
      Eq-Premetric
        ( tr (Premetric l2) e (structure-Premetric-Space A))
        ( structure-Premetric-Space B)
    backward I d x y =
      logical-equivalence-reasoning
        ( is-close-Premetric
          ( tr (Premetric l2) e (structure-Premetric-Space A))
          ( d)
          ( x)
          ( y))
        ↔ ( is-close-Premetric
            ( structure-Premetric-Space A)
            ( d)
            ( map-inv-eq e x)
            ( map-inv-eq e y))
          by
            eq-map-inv-eq-tr-Premetric
              ( type-Premetric-Space A)
              ( type-Premetric-Space B)
              ( e)
              ( structure-Premetric-Space A)
              ( d)
              ( x)
              ( y)
        ↔ ( is-close-Premetric-Space
            ( B)
            ( d)
            ( map-eq e (map-inv-eq e x))
            ( map-eq e (map-inv-eq e y)))
          by
            I d (map-inv-eq e x) (map-inv-eq e y)
        ↔ ( is-close-Premetric-Space B d x y)
          by
            binary-tr
              ( λ u v →
                is-close-Premetric-Space B d u v ↔
                is-close-Premetric-Space B d x y)
              ( inv (is-section-map-inv-equiv (equiv-eq e) x))
              ( inv (is-section-map-inv-equiv (equiv-eq e) y))
              ( id-iff)
```

### Equality of premetric spaces is equivalent to isometric equality of their carrier types

```agda
module _
  {l1 l2 : Level} (A B : Premetric-Space l1 l2)
  where

  equiv-isometric-eq-Premetric-Space :
    (A ＝ B) ≃ isometric-eq-Premetric-Space A B
  equiv-isometric-eq-Premetric-Space =
    ( equiv-tot (equiv-is-isometry-map-eq-tr-Premetric-Space A B)) ∘e
    ( equiv-eq-tr-Premetric-Space A B)

  eq-isometric-eq-Premetric-Space :
    isometric-eq-Premetric-Space A B → A ＝ B
  eq-isometric-eq-Premetric-Space =
    map-inv-equiv equiv-isometric-eq-Premetric-Space
```

### Isometric equality of premetric spaces is torsorial

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  where

  is-torsorial-isometric-eq-Premetric-Space :
    is-torsorial (isometric-eq-Premetric-Space A)
  is-torsorial-isometric-eq-Premetric-Space =
    is-contr-equiv'
      ( Σ (Premetric-Space l1 l2) (Id A))
      ( equiv-tot (equiv-isometric-eq-Premetric-Space A))
      ( is-torsorial-Id A)
```
