# Discrete metric spaces

```agda
module metric-spaces.discrete-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
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

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensional-pseudometric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.locally-constant-functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.preimage-rational-neighborhoods
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhoods
open import metric-spaces.reflexive-rational-neighborhoods
open import metric-spaces.saturated-rational-neighborhoods
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
open import metric-spaces.symmetric-rational-neighborhoods
open import metric-spaces.triangular-rational-neighborhoods
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) is called
{{#concept "discrete" Disambiguation="metric space" Agda=is-discrete-Metric-Space}}
if all
[elements at bounded distance](metric-spaces.elements-at-bounded-distance-metric-spaces.md)
are [equal](foundation.identity-types.md). Discrete metric spaces are
[complete](metric-spaces.complete-metric-spaces.md) and any discrete metric
space is [isometrically equal](metric-spaces.equality-of-metric-spaces.md) to
the
{{#concept "standard discrete metric space" Disambiguation="on a set" Agda=discrete-metric-space-Set}}
on its underlying [set](foundation.sets.md).

Any [map](metric-spaces.functions-metric-spaces.md) from a discrete metric space
is [short](metric-spaces.short-functions-metric-spaces.md); a map into a
discrete metric space is short if and only if it is
[locally constant](metric-spaces.locally-constant-functions-metric-spaces.md).

## Definitions

### The property of being a discrete metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-discrete-prop-Metric-Space : Prop (l1 ⊔ l2)
  is-discrete-prop-Metric-Space =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( type-Metric-Space A)
          ( λ x →
            Π-Prop
              ( type-Metric-Space A)
              ( λ y →
                hom-Prop
                  ( neighborhood-prop-Metric-Space A d x y)
                  ( Id-Prop
                    ( set-Metric-Space A)
                    ( x)
                    ( y)))))

  is-discrete-Metric-Space : UU (l1 ⊔ l2)
  is-discrete-Metric-Space =
    type-Prop is-discrete-prop-Metric-Space

  is-prop-is-discrete-Metric-Space :
    is-prop is-discrete-Metric-Space
  is-prop-is-discrete-Metric-Space =
    is-prop-type-Prop is-discrete-prop-Metric-Space
```

### The type of discrete metric spaces

```agda
Discrete-Metric-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Discrete-Metric-Space l1 l2 = Σ (Metric-Space l1 l2) is-discrete-Metric-Space

module _
  {l1 l2 : Level} (A : Discrete-Metric-Space l1 l2)
  where

  metric-space-Discrete-Metric-Space : Metric-Space l1 l2
  metric-space-Discrete-Metric-Space = pr1 A

  is-discrete-metric-space-Discrete-Metric-Space :
    is-discrete-Metric-Space metric-space-Discrete-Metric-Space
  is-discrete-metric-space-Discrete-Metric-Space = pr2 A

  set-Discrete-Metric-Space : Set l1
  set-Discrete-Metric-Space =
    set-Metric-Space metric-space-Discrete-Metric-Space

  type-Discrete-Metric-Space : UU l1
  type-Discrete-Metric-Space =
    type-Metric-Space metric-space-Discrete-Metric-Space
```

### The canonical discrete metric structure on a set

```agda
module _
  {l : Level} (A : Set l)
  where

  discrete-neighborhood-prop-Set :
    Rational-Neighborhood-Relation l (type-Set A)
  discrete-neighborhood-prop-Set _ x y = Id-Prop A x y

  discrete-neighborhood-Set : ℚ⁺ → type-Set A → type-Set A → UU l
  discrete-neighborhood-Set _ x y = x ＝ y

  is-reflexive-discrete-neighborhood-Set :
    is-reflexive-Rational-Neighborhood-Relation discrete-neighborhood-prop-Set
  is-reflexive-discrete-neighborhood-Set _ x = refl

  is-symmetric-discrete-neighborhood-Set :
    is-symmetric-Rational-Neighborhood-Relation discrete-neighborhood-prop-Set
  is-symmetric-discrete-neighborhood-Set _ x y = inv

  is-triangluar-discrete-neighborhood-Set :
    is-triangular-Rational-Neighborhood-Relation discrete-neighborhood-prop-Set
  is-triangluar-discrete-neighborhood-Set x y z _ _ H K = K ∙ H

  is-saturated-discrete-neighborhood-Set :
    is-saturated-Rational-Neighborhood-Relation discrete-neighborhood-prop-Set
  is-saturated-discrete-neighborhood-Set _ x y H = H one-ℚ⁺

  discrete-pseudometric-Set : Pseudometric-Space l l
  discrete-pseudometric-Set =
    ( type-Set A) ,
    ( discrete-neighborhood-prop-Set) ,
    ( is-reflexive-discrete-neighborhood-Set) ,
    ( is-symmetric-discrete-neighborhood-Set) ,
    ( is-triangluar-discrete-neighborhood-Set) ,
    ( is-saturated-discrete-neighborhood-Set)

  is-tight-discrete-pseudometric-space-Set :
    is-tight-Pseudometric-Space discrete-pseudometric-Set
  is-tight-discrete-pseudometric-space-Set x y H = H one-ℚ⁺

  is-extensional-discrete-pseudometric-space-Set :
    is-extensional-Pseudometric-Space discrete-pseudometric-Set
  is-extensional-discrete-pseudometric-space-Set =
    is-extensional-is-tight-Pseudometric-Space
      discrete-pseudometric-Set
      is-tight-discrete-pseudometric-space-Set

  metric-space-discrete-metric-space-Set : Metric-Space l l
  metric-space-discrete-metric-space-Set =
    make-Metric-Space
      ( type-Set A)
      ( discrete-neighborhood-prop-Set)
      ( is-reflexive-discrete-neighborhood-Set)
      ( is-symmetric-discrete-neighborhood-Set)
      ( is-triangluar-discrete-neighborhood-Set)
      ( is-saturated-discrete-neighborhood-Set)
      ( is-extensional-discrete-pseudometric-space-Set)

  is-discrete-metric-space-discrete-metric-space-Set :
    is-discrete-Metric-Space metric-space-discrete-metric-space-Set
  is-discrete-metric-space-discrete-metric-space-Set _ _ _ = id

  discrete-metric-space-Set : Discrete-Metric-Space l l
  discrete-metric-space-Set =
    metric-space-discrete-metric-space-Set ,
    is-discrete-metric-space-discrete-metric-space-Set
```

## Properties

### Any discrete metric space is isometrically equal to the standard discrete metric space on its underlying set

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (H : is-discrete-Metric-Space A)
  where

  isometric-eq-discrete-metric-space-is-discrete-Metric-Space :
    isometric-eq-Metric-Space
      ( metric-space-discrete-metric-space-Set (set-Metric-Space A))
      ( A)
  isometric-eq-discrete-metric-space-is-discrete-Metric-Space =
    ( refl) ,
    ( λ d x y →
      ( λ N → sim-eq-Metric-Space A x y N d) ,
      ( H d x y))
```

### Discrete metric spaces are equivalent to sets

```agda
module _
  {l : Level}
  where

  is-equiv-discrete-metric-space-Set : is-equiv (discrete-metric-space-Set {l})
  is-equiv-discrete-metric-space-Set =
    is-equiv-is-invertible
      ( set-Discrete-Metric-Space)
      ( λ A →
        eq-type-subtype
          ( is-discrete-prop-Metric-Space)
          ( eq-isometric-eq-Metric-Space
            ( metric-space-discrete-metric-space-Set
              ( set-Discrete-Metric-Space A))
            ( metric-space-Discrete-Metric-Space A)
            ( isometric-eq-discrete-metric-space-is-discrete-Metric-Space
              ( metric-space-Discrete-Metric-Space A)
              ( is-discrete-metric-space-Discrete-Metric-Space A))))
      ( λ _ → eq-type-subtype is-set-Prop refl)

  equiv-Set-Discrete-Metric-Space : Set l ≃ Discrete-Metric-Space l l
  equiv-Set-Discrete-Metric-Space =
    discrete-metric-space-Set , is-equiv-discrete-metric-space-Set
```

### Cauchy approximations in a discrete metric space are weakly constant

```agda
module _
  {l1 l2 : Level} (A : Discrete-Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space (metric-space-Discrete-Metric-Space A))
  where

  is-wconstant-cauchy-approximation-Discrete-Metric-Space :
    (ε δ : ℚ⁺) →
    Id
      ( map-cauchy-approximation-Metric-Space
        ( metric-space-Discrete-Metric-Space A)
        ( f)
        ( ε))
      ( map-cauchy-approximation-Metric-Space
        ( metric-space-Discrete-Metric-Space A)
        ( f)
        ( δ))
  is-wconstant-cauchy-approximation-Discrete-Metric-Space ε δ =
    is-discrete-metric-space-Discrete-Metric-Space
      ( A)
      ( ε +ℚ⁺ δ)
      ( map-cauchy-approximation-Metric-Space
        ( metric-space-Discrete-Metric-Space A)
        ( f)
        ( ε))
      ( map-cauchy-approximation-Metric-Space
        ( metric-space-Discrete-Metric-Space A)
        ( f)
        ( δ))
      ( is-cauchy-approximation-map-cauchy-approximation-Metric-Space
        ( metric-space-Discrete-Metric-Space A)
        ( f)
        ( ε)
        ( δ))
```

### Any discrete metric space is complete

```agda
module _
  {l1 l2 : Level}
  where

  is-complete-is-discrete-Metric-Space :
    (A : Metric-Space l1 l2) →
    is-discrete-Metric-Space A →
    is-complete-Metric-Space A
  is-complete-is-discrete-Metric-Space A H f =
    ( map-cauchy-approximation-Metric-Space A f one-ℚ⁺) ,
    ( λ ε →
      refl-eq-neighborhood-Metric-Space A ε
        ( H
          ( ε +ℚ⁺ one-ℚ⁺)
          ( map-cauchy-approximation-Metric-Space A f ε)
          ( map-cauchy-approximation-Metric-Space A f one-ℚ⁺)
          ( is-cauchy-approximation-map-cauchy-approximation-Metric-Space
            ( A)
            ( f)
            ( ε)
            ( one-ℚ⁺))))

  complete-Discrete-Metric-Space :
    Discrete-Metric-Space l1 l2 → Complete-Metric-Space l1 l2
  complete-Discrete-Metric-Space =
    tot is-complete-is-discrete-Metric-Space
```

### Characterization of short maps from/to discrete metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level} (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : type-function-Metric-Space A B)
  where

  is-short-is-discrete-domain-function-Metric-Space :
    is-discrete-Metric-Space A →
    is-short-function-Metric-Space A B f
  is-short-is-discrete-domain-function-Metric-Space H d x y Nxy =
    sim-eq-Metric-Space
      ( B)
      ( f x)
      ( f y)
      ( ap f (H d x y Nxy))
      ( d)

  is-locally-constant-is-short-is-discrete-codomain-function-Metric-Space :
    is-discrete-Metric-Space B →
    is-short-function-Metric-Space A B f →
    is-locally-constant-function-Metric-Space A B f
  is-locally-constant-is-short-is-discrete-codomain-function-Metric-Space
    H K x y =
    elim-exists
      ( Id-Prop (set-Metric-Space B) (f x) (f y))
      ( λ d → H d (f x) (f y) ∘ (K d x y))

  iff-is-locally-constant-is-short-is-discrete-codomain-function-Metric-Space :
    is-discrete-Metric-Space B →
    is-short-function-Metric-Space A B f ↔
    is-locally-constant-function-Metric-Space A B f
  iff-is-locally-constant-is-short-is-discrete-codomain-function-Metric-Space
    H =
    ( is-locally-constant-is-short-is-discrete-codomain-function-Metric-Space
      H) ,
    ( is-short-is-locally-constant-function-Metric-Space A B f)
```
