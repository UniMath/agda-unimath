# Dependent products of metric spaces (WIP)

```agda
module metric-spaces.dependent-products-metric-spaces-WIP where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces-WIP
open import metric-spaces.complete-metric-spaces-WIP
open import metric-spaces.convergent-cauchy-approximations-metric-spaces-WIP
open import metric-spaces.extensional-pseudometric-spaces-WIP
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces-WIP
open import metric-spaces.metric-spaces-WIP
open import metric-spaces.monotonic-rational-neighborhoods
open import metric-spaces.pseudometric-spaces-WIP
open import metric-spaces.rational-neighborhoods
open import metric-spaces.reflexive-rational-neighborhoods
open import metric-spaces.saturated-rational-neighborhoods
open import metric-spaces.short-functions-metric-spaces-WIP
open import metric-spaces.symmetric-rational-neighborhoods
open import metric-spaces.triangular-rational-neighborhoods
```

</details>

## Idea

A family of [metric spaces](metric-spaces.metric-spaces.md) over a type produces
a {{#concept "product metric space" Agda=Π-Metric-Space-WIP}} on the type of
dependent functions into the carrier types of the family. Two functions `f` and
`g` are in a [`d`-neighborhood](metric-spaces.premetric-structures.md) in the
product structure if this holds for all the evaluations `f x` and `g x`. I.e
this is the premetric such that
[upper bounds](metric-spaces.premetric-structures.md) on the distance between
`f` and `g` are bounded below by the supremum of the distances between each
`f x` and `g x`. The evaluation functions from the product metric space to each
projected metric space are
[short maps](metric-spaces.short-functions-metric-spaces.md).

## Definitions

### Product of metric spaces

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space-WIP l1 l2)
  where

  type-Π-Metric-Space-WIP : UU (l ⊔ l1)
  type-Π-Metric-Space-WIP = (x : A) → type-Metric-Space-WIP (P x)

  neighborhood-prop-Π-Metric-Space-WIP :
    Rational-Neighborhood-Relation (l ⊔ l2) type-Π-Metric-Space-WIP
  neighborhood-prop-Π-Metric-Space-WIP d f g =
    Π-Prop A (λ x → neighborhood-prop-Metric-Space-WIP (P x) d (f x) (g x))

  is-reflexive-neighborhood-Π-Metric-Space-WIP :
    is-reflexive-Rational-Neighborhood-Relation
      neighborhood-prop-Π-Metric-Space-WIP
  is-reflexive-neighborhood-Π-Metric-Space-WIP d f a =
    refl-neighborhood-Metric-Space-WIP (P a) d (f a)

  is-symmetric-neighborhood-Π-Metric-Space-WIP :
    is-symmetric-Rational-Neighborhood-Relation
      neighborhood-prop-Π-Metric-Space-WIP
  is-symmetric-neighborhood-Π-Metric-Space-WIP d f g H a =
    symmetric-neighborhood-Metric-Space-WIP (P a) d (f a) (g a) (H a)

  is-triangular-neighborhood-Π-Metric-Space-WIP :
    is-triangular-Rational-Neighborhood-Relation
      neighborhood-prop-Π-Metric-Space-WIP
  is-triangular-neighborhood-Π-Metric-Space-WIP f g h d₁ d₂ H K a =
    triangular-neighborhood-Metric-Space-WIP
      ( P a)
      ( f a)
      ( g a)
      ( h a)
      ( d₁)
      ( d₂)
      ( H a)
      ( K a)

  is-saturated-neighborhood-Π-Metric-Space-WIP :
    is-saturated-Rational-Neighborhood-Relation
      neighborhood-prop-Π-Metric-Space-WIP
  is-saturated-neighborhood-Π-Metric-Space-WIP ε x y H a =
    saturated-neighborhood-Metric-Space-WIP
      ( P a)
      ( ε)
      ( x a)
      ( y a)
      ( λ d → H d a)

  pseudometric-space-Π-Metric-Space : Pseudometric-Space-WIP (l ⊔ l1) (l ⊔ l2)
  pseudometric-space-Π-Metric-Space =
    ( type-Π-Metric-Space-WIP) ,
    ( neighborhood-prop-Π-Metric-Space-WIP ,
      is-reflexive-neighborhood-Π-Metric-Space-WIP ,
      is-symmetric-neighborhood-Π-Metric-Space-WIP ,
      is-triangular-neighborhood-Π-Metric-Space-WIP ,
      is-saturated-neighborhood-Π-Metric-Space-WIP)

  is-extensional-pseudometric-space-Π-Metric-Space :
    is-extensional-Pseudometric-Space-WIP
      pseudometric-space-Π-Metric-Space
  is-extensional-pseudometric-space-Π-Metric-Space =
    is-extensional-is-tight-Pseudometric-Space
      ( pseudometric-space-Π-Metric-Space)
      ( λ f g H →
        eq-htpy
          ( λ a →
            eq-sim-Metric-Space-WIP
              ( P a)
              ( f a)
              ( g a)
              ( λ d → H d a)))

  Π-Metric-Space-WIP : Metric-Space-WIP (l ⊔ l1) (l ⊔ l2)
  Π-Metric-Space-WIP =
    make-Metric-Space-WIP
      type-Π-Metric-Space-WIP
      neighborhood-prop-Π-Metric-Space-WIP
      is-reflexive-neighborhood-Π-Metric-Space-WIP
      is-symmetric-neighborhood-Π-Metric-Space-WIP
      is-triangular-neighborhood-Π-Metric-Space-WIP
      is-saturated-neighborhood-Π-Metric-Space-WIP
      is-extensional-pseudometric-space-Π-Metric-Space
```

## Properties

### The evaluation maps on a product metric space are short

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space-WIP l1 l2) (a : A)
  where

  is-short-ev-Π-Metric-Space-WIP :
    is-short-function-Metric-Space-WIP
      ( Π-Metric-Space-WIP A P)
      ( P a)
      ( ev a)
  is-short-ev-Π-Metric-Space-WIP ε x y H = H a

  short-ev-Π-Metric-Space-WIP :
    short-function-Metric-Space-WIP
      ( Π-Metric-Space-WIP A P)
      ( P a)
  short-ev-Π-Metric-Space-WIP = (ev a) , (is-short-ev-Π-Metric-Space-WIP)
```

### The partial applications of a Cauchy approximation in a dependent product metric space are Cauchy approximations

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space-WIP l1 l2)
  (f : cauchy-approximation-Metric-Space-WIP (Π-Metric-Space-WIP A P))
  where

  ev-cauchy-approximation-Π-Metric-Space-WIP :
    (x : A) → cauchy-approximation-Metric-Space-WIP (P x)
  ev-cauchy-approximation-Π-Metric-Space-WIP x =
    map-short-function-cauchy-approximation-Metric-Space-WIP
      ( Π-Metric-Space-WIP A P)
      ( P x)
      ( short-ev-Π-Metric-Space-WIP A P x)
      ( f)
```

### A dependent map is the limit of a Cauchy approximation in a dependent product of metric spaces if and only if it is the pointwise limit of its partial applications

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space-WIP l1 l2)
  (f : cauchy-approximation-Metric-Space-WIP (Π-Metric-Space-WIP A P))
  (g : type-Π-Metric-Space-WIP A P)
  where

  is-pointwise-limit-is-limit-cauchy-approximation-Π-Metric-Space-WIP :
    is-limit-cauchy-approximation-Metric-Space-WIP
      ( Π-Metric-Space-WIP A P)
      ( f)
      ( g) →
    (x : A) →
    is-limit-cauchy-approximation-Metric-Space-WIP
      ( P x)
      ( ev-cauchy-approximation-Π-Metric-Space-WIP A P f x)
      ( g x)
  is-pointwise-limit-is-limit-cauchy-approximation-Π-Metric-Space-WIP L x ε δ =
    L ε δ x

  is-limit-is-pointwise-limit-cauchy-approximation-Π-Metric-Space-WIP :
    ( (x : A) →
      is-limit-cauchy-approximation-Metric-Space-WIP
        ( P x)
        ( ev-cauchy-approximation-Π-Metric-Space-WIP A P f x)
        ( g x)) →
    is-limit-cauchy-approximation-Metric-Space-WIP
      ( Π-Metric-Space-WIP A P)
      ( f)
      ( g)
  is-limit-is-pointwise-limit-cauchy-approximation-Π-Metric-Space-WIP L ε δ x =
    L x ε δ
```

### A product of complete metric spaces is complete

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space-WIP l1 l2)
  (Π-complete : (x : A) → is-complete-Metric-Space-WIP (P x))
  where

  limit-cauchy-approximation-Π-is-complete-Metric-Space-WIP :
    cauchy-approximation-Metric-Space-WIP (Π-Metric-Space-WIP A P) →
    type-Π-Metric-Space-WIP A P
  limit-cauchy-approximation-Π-is-complete-Metric-Space-WIP u x =
    limit-cauchy-approximation-Complete-Metric-Space-WIP
      ( P x , Π-complete x)
      ( ev-cauchy-approximation-Π-Metric-Space-WIP A P u x)

  is-limit-limit-cauchy-approximation-Π-is-complete-Metric-Space-WIP :
    (u : cauchy-approximation-Metric-Space-WIP (Π-Metric-Space-WIP A P)) →
    is-limit-cauchy-approximation-Metric-Space-WIP
      ( Π-Metric-Space-WIP A P)
      ( u)
      ( limit-cauchy-approximation-Π-is-complete-Metric-Space-WIP u)
  is-limit-limit-cauchy-approximation-Π-is-complete-Metric-Space-WIP u ε δ x =
    is-limit-limit-cauchy-approximation-Complete-Metric-Space-WIP
      ( P x , Π-complete x)
      ( ev-cauchy-approximation-Π-Metric-Space-WIP A P u x)
      ( ε)
      ( δ)

  is-complete-Π-Metric-Space-WIP :
    is-complete-Metric-Space-WIP (Π-Metric-Space-WIP A P)
  is-complete-Π-Metric-Space-WIP u =
    limit-cauchy-approximation-Π-is-complete-Metric-Space-WIP u ,
    is-limit-limit-cauchy-approximation-Π-is-complete-Metric-Space-WIP u
```

### The complete product of complete metric spaces

```agda
module _
  {l l1 l2 : Level} (A : UU l) (C : A → Complete-Metric-Space-WIP l1 l2)
  where

  Π-Complete-Metric-Space-WIP : Complete-Metric-Space-WIP (l ⊔ l1) (l ⊔ l2)
  pr1 Π-Complete-Metric-Space-WIP =
    Π-Metric-Space-WIP A (metric-space-Complete-Metric-Space-WIP ∘ C)
  pr2 Π-Complete-Metric-Space-WIP =
    is-complete-Π-Metric-Space-WIP
      ( A)
      ( metric-space-Complete-Metric-Space-WIP ∘ C)
      ( is-complete-metric-space-Complete-Metric-Space-WIP ∘ C)
```
