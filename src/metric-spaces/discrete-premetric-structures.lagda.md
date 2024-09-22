# Discrete premetric structures

```agda
module metric-spaces.discrete-premetric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.premetric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

A [premetric](metric-spaces.md) on a type `A` is
{{#concept "discrete" Disambiguation="premetric structure" Agda=is-discrete-Premetric}}
any elements in some [`d`-neighborhood](metric-spaces.premetric-structures.md)
are [merely equal](foundation.mere-equality.md).

In a discrete premetric, two points are at bounded distance if and only iff they
are merely equal, in which case all positive rational numbers are upper bounds
on their distance.

Every type has a unique reflexive discrete premetric.

## Definitions

### The property of being a discrete premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-discrete-prop-Premetric : Prop (l1 ⊔ l2)
  is-discrete-prop-Premetric =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( A)
          ( λ x →
            Π-Prop
              ( A)
              ( λ y →
                hom-Prop
                  ( B d x y)
                  ( trunc-Prop (x ＝ y)))))

  is-discrete-Premetric : UU (l1 ⊔ l2)
  is-discrete-Premetric = type-Prop is-discrete-prop-Premetric

  is-prop-is-discrete-Premetric : is-prop is-discrete-Premetric
  is-prop-is-discrete-Premetric =
    is-prop-type-Prop is-discrete-prop-Premetric
```

### The standard discrete premetric on a type

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  discrete-Premetric : Premetric l1 A
  discrete-Premetric d x y = trunc-Prop (x ＝ y)

  is-discrete-discrete-Premetric :
    is-discrete-Premetric discrete-Premetric
  is-discrete-discrete-Premetric d x y H = H
```

## Properties

### The standard discrete premetric on a type is reflexive

```agda
module _
  {l : Level} (A : UU l)
  where

  is-reflexive-discrete-Premetric :
    is-reflexive-Premetric (discrete-Premetric A)
  is-reflexive-discrete-Premetric d x =
    unit-trunc-Prop refl
```

### The standard discrete premetric on a type is symmetric

```agda
module _
  {l : Level} (A : UU l)
  where

  is-symmetric-discrete-Premetric :
    is-symmetric-Premetric (discrete-Premetric A)
  is-symmetric-discrete-Premetric d x y =
    rec-trunc-Prop
      ( trunc-Prop (y ＝ x))
      ( unit-trunc-Prop ∘ inv)
```

### The standard discrete premetric on a type is triangular

```agda
module _
  {l : Level} (A : UU l)
  where

  is-triangular-discrete-Premetric :
    is-triangular-Premetric (discrete-Premetric A)
  is-triangular-discrete-Premetric x y z d₁ d₂ H =
    rec-trunc-Prop
      ( trunc-Prop (x ＝ z))
      ( λ (i : x ＝ y) →
        rec-trunc-Prop
          ( trunc-Prop (x ＝ z))
          ( λ (j : y ＝ z) → unit-trunc-Prop (i ∙ j))
          ( H))
```

### Any type has a unique reflexive discrete premetric

```agda
module _
  {l : Level} {A : UU l} (B : Premetric l A)
  (R : is-reflexive-Premetric B)
  (D : is-discrete-Premetric B)
  where

  eq-discrete-is-discrete-reflexive-Premetric : B ＝ (discrete-Premetric A)
  eq-discrete-is-discrete-reflexive-Premetric =
    eq-Eq-Premetric
      ( B)
      ( discrete-Premetric A)
      ( λ d x y →
        ( ( D d x y) ,
          ( rec-trunc-Prop
            ( B d x y)
            ( λ e → indistinguishable-eq-reflexive-Premetric B R e d))))
```
