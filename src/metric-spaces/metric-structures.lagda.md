# Metric structures

```agda
module metric-spaces.metric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import metric-spaces.neighbourhood-relations
```

</details>

## Idea

A {{#concept "metric structure" Agda=Metric-Structure}} on a type is a symmetric
reflexive separating triangular
[neighbourhood-relation](metric-spaces.neighbourhood-relations.md).

## Definitions

### The property of being a metric neighbourhood-relation on a type

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : neighbourhood-Relation-Prop l2 A)
  where

  is-metric-neighbourhood : UU (l1 ⊔ l2)
  is-metric-neighbourhood =
    ( is-symmetric-neighbourhood B) ×
    ( is-reflexive-neighbourhood B) ×
    ( is-separating-neighbourhood B) ×
    ( is-triangular-neighbourhood B)

  is-prop-is-metric-neighbourhood : is-prop is-metric-neighbourhood
  is-prop-is-metric-neighbourhood =
    is-prop-product
      ( is-prop-is-symmetric-neighbourhood B)
      ( is-prop-product
        ( is-prop-is-reflexive-neighbourhood B)
        ( is-prop-product
          ( is-prop-is-separating-neighbourhood B)
          ( is-prop-is-triangular-neighbourhood B)))

  is-metric-prop-neighbourhood : Prop (l1 ⊔ l2)
  is-metric-prop-neighbourhood =
    is-metric-neighbourhood , is-prop-is-metric-neighbourhood
```

### Metric structures over a type

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  Metric-Structure : UU (l1 ⊔ lsuc l2)
  Metric-Structure = type-subtype (is-metric-prop-neighbourhood {l1} {l2} A)
```

### Neighbourhood relation of a metric structure

```agda
module _
  {l1 l2 : Level} (A : UU l1) (S : Metric-Structure l2 A)
  where

  neighbourhood-Metric-Structure : neighbourhood-Relation-Prop l2 A
  neighbourhood-Metric-Structure = pr1 S

  is-in-neighbourhood-prop-Metric-Structure : ℚ⁺ → A → A → Prop l2
  is-in-neighbourhood-prop-Metric-Structure d x y =
    neighbourhood-Metric-Structure d x y

  is-in-neighbourhood-Metric-Structure : ℚ⁺ → A → A → UU l2
  is-in-neighbourhood-Metric-Structure d x y =
    type-Prop (is-in-neighbourhood-prop-Metric-Structure d x y)

  is-prop-is-in-neighbourhood-Metric-Structure :
    (d : ℚ⁺) (x y : A) → is-prop (is-in-neighbourhood-Metric-Structure d x y)
  is-prop-is-in-neighbourhood-Metric-Structure d x y =
    is-prop-type-Prop (is-in-neighbourhood-prop-Metric-Structure d x y)

  is-metric-neighbourhood-Metric-Structure :
    is-metric-neighbourhood A neighbourhood-Metric-Structure
  is-metric-neighbourhood-Metric-Structure = pr2 S
```

## Properties

### Equality of metric structures

```agda
module _
  {l1 l2 : Level} (A : UU l1) (S : Metric-Structure l2 A)
  where

  Eq-prop-Metric-Structure : (S' : Metric-Structure l2 A) → Prop (l1 ⊔ l2)
  Eq-prop-Metric-Structure S' =
    Eq-prop-neighbourhood-Relation-Prop
      ( A)
      ( neighbourhood-Metric-Structure A S)
      ( pr1 S')

  Eq-Metric-Structure : (S' : Metric-Structure l2 A) → UU (l1 ⊔ l2)
  Eq-Metric-Structure S' = type-Prop (Eq-prop-Metric-Structure S')

  is-prop-Eq-Metric-Structure :
    (S' : Metric-Structure l2 A) → is-prop (Eq-Metric-Structure S')
  is-prop-Eq-Metric-Structure S' =
    is-prop-type-Prop (Eq-prop-Metric-Structure S')

  refl-Eq-Metric-Structure : Eq-Metric-Structure S
  refl-Eq-Metric-Structure d x y = id-iff

  Eq-eq-Metric-Structure :
    (S' : Metric-Structure l2 A) → S ＝ S' → Eq-Metric-Structure S'
  Eq-eq-Metric-Structure .S refl = refl-Eq-Metric-Structure

  is-torsorial-Eq-Metric-Structure : is-torsorial Eq-Metric-Structure
  is-torsorial-Eq-Metric-Structure =
    ( S , refl-Eq-Metric-Structure) ,
    ( eq-type-subtype Eq-prop-Metric-Structure ∘
      eq-type-subtype (is-metric-prop-neighbourhood A) ∘
      λ (S' , e) →
      eq-neighbourhood-Relation
        ( A)
        ( neighbourhood-Metric-Structure A S)
        ( pr1 S')
        ( e))

  is-equiv-Eq-eq-Metric-Structure :
    (S' : Metric-Structure l2 A) → is-equiv (Eq-eq-Metric-Structure S')
  is-equiv-Eq-eq-Metric-Structure =
    fundamental-theorem-id
      is-torsorial-Eq-Metric-Structure
      Eq-eq-Metric-Structure

  equiv-Eq-eq-Metric-Structure :
    (S' : Metric-Structure l2 A) → (S ＝ S') ≃ Eq-Metric-Structure S'
  equiv-Eq-eq-Metric-Structure S' =
    Eq-eq-Metric-Structure S' , is-equiv-Eq-eq-Metric-Structure S'
```

### Any set can be equipped with a metric structure

```agda
module _
  {l : Level} (A : Set l)
  where

  discrete-Metric-Structure : Metric-Structure l (type-Set A)
  pr1 discrete-Metric-Structure d = Id-Prop A
  pr2 discrete-Metric-Structure =
    ( λ d x y H → inv H) ,
    ( λ d x → refl) ,
    ( is-separating-is-tight-neighbourhood
      ( λ d → Id-Prop A)
      ( λ x y H → H one-ℚ⁺)) ,
    ( λ x y z d₁ d₂ H K → K ∙ H)
```
