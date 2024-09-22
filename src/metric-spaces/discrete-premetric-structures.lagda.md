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

Any type comes equipped with a canonical
{{#concept "discrete" Disambiguation="premetric structure" Agda=is-discrete-Premetric}}
[premetric](metric-spaces.premetric-structures.md) where `d`-neighbors are
[merely equal](foundation.mere-equality.md) elements. This is the unique
reflexive premetric such that two points are at bounded distance if and only if
they are merely equal, in which case they are indistinguishable.

## Definitions

### The property of being a semidiscrete premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-semidiscrete-prop-Premetric : Prop (l1 ⊔ l2)
  is-semidiscrete-prop-Premetric =
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

  is-semidiscrete-Premetric : UU (l1 ⊔ l2)
  is-semidiscrete-Premetric = type-Prop is-semidiscrete-prop-Premetric

  is-prop-is-semidiscrete-Premetric : is-prop is-semidiscrete-Premetric
  is-prop-is-semidiscrete-Premetric =
    is-prop-type-Prop is-semidiscrete-prop-Premetric
```

### The property of being a discrete premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-discrete-prop-Premetric : Prop (l1 ⊔ l2)
  is-discrete-prop-Premetric =
    product-Prop
      ( is-reflexive-prop-Premetric B)
      ( is-semidiscrete-prop-Premetric B)

  is-discrete-Premetric : UU (l1 ⊔ l2)
  is-discrete-Premetric = type-Prop is-discrete-prop-Premetric

  is-prop-is-discrete-Premetric : is-prop is-discrete-Premetric
  is-prop-is-discrete-Premetric =
    is-prop-type-Prop is-discrete-prop-Premetric
```

### The cannonical discrete premetric on a type

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  discrete-Premetric : Premetric l1 A
  discrete-Premetric d x y = trunc-Prop (x ＝ y)

  is-discrete-discrete-Premetric :
    is-discrete-Premetric discrete-Premetric
  is-discrete-discrete-Premetric =
    (λ x d → unit-trunc-Prop refl) ,
    (λ d x y → id)
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

### Neighbors in the discrete premetric are indistinguishable

```agda
module _
  {l : Level} (A : UU l) (d : ℚ⁺) (x y : A)
  where

  is-indistinguishable-is-in-neighborhood-discrete-Premetric :
    neighborhood-Premetric (discrete-Premetric A) d x y →
    is-indistinguishable-Premetric (discrete-Premetric A) x y
  is-indistinguishable-is-in-neighborhood-discrete-Premetric H d = H
```

### Any type has a unique reflexive discrete premetric

```agda
module _
  {l : Level} {A : UU l}
  where

  eq-discrete-is-discrete-Premetric :
    (B : Premetric l A) (D : is-discrete-Premetric B) →
    ((discrete-Premetric A) ＝ B)
  eq-discrete-is-discrete-Premetric B D =
    eq-Eq-Premetric
      ( discrete-Premetric A)
      ( B)
      ( λ d x y →
        ( ( rec-trunc-Prop
            ( B d x y)
            ( λ e → indistinguishable-eq-reflexive-Premetric B (pr1 D) e d)) ,
          ( pr2 D d x y)))

  is-contr-discrete-Premetric :
    is-contr (Σ (Premetric l A) (is-discrete-Premetric))
  is-contr-discrete-Premetric =
    ( discrete-Premetric A , is-discrete-discrete-Premetric A) ,
    ( λ (B , H) →
      eq-type-subtype
        ( is-discrete-prop-Premetric)
        ( eq-discrete-is-discrete-Premetric B H))
```
