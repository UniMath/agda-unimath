# Dependent products of metric spaces

```agda
module metric-spaces.dependent-products-metric-spaces where
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

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.extensional-premetric-structures
open import metric-spaces.limits-of-cauchy-approximations-premetric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.premetric-structures
open import metric-spaces.pseudometric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.saturated-metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

A family of [metric spaces](metric-spaces.metric-spaces.md) over a type produces
a {{#concept "product metric space" Agda=Π-Metric-Space}} on the type of
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
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space l1 l2)
  where

  type-Π-Metric-Space : UU (l ⊔ l1)
  type-Π-Metric-Space = (x : A) → type-Metric-Space (P x)

  structure-Π-Metric-Space : Premetric (l ⊔ l2) type-Π-Metric-Space
  structure-Π-Metric-Space d f g =
    Π-Prop A (λ x → structure-Metric-Space (P x) d (f x) (g x))

  is-reflexive-structure-Π-Metric-Space :
    is-reflexive-Premetric structure-Π-Metric-Space
  is-reflexive-structure-Π-Metric-Space d f a =
    is-reflexive-structure-Metric-Space (P a) d (f a)

  is-symmetric-structure-Π-Metric-Space :
    is-symmetric-Premetric structure-Π-Metric-Space
  is-symmetric-structure-Π-Metric-Space d f g H a =
    is-symmetric-structure-Metric-Space (P a) d (f a) (g a) (H a)

  is-triangular-structure-Π-Metric-Space :
    is-triangular-Premetric structure-Π-Metric-Space
  is-triangular-structure-Π-Metric-Space f g h d₁ d₂ H K a =
    is-triangular-structure-Metric-Space
      ( P a)
      ( f a)
      ( g a)
      ( h a)
      ( d₁)
      ( d₂)
      ( H a)
      ( K a)

  is-local-structure-Π-Metric-Space :
    is-local-Premetric structure-Π-Metric-Space
  is-local-structure-Π-Metric-Space =
    is-local-is-tight-Premetric
      ( structure-Π-Metric-Space)
      ( λ f g H →
        eq-htpy
          ( λ a →
            is-tight-structure-Metric-Space
              ( P a)
              ( f a)
              ( g a)
              ( λ d → H d a)))

  is-pseudometric-structure-Π-Metric-Space :
    is-pseudometric-Premetric structure-Π-Metric-Space
  is-pseudometric-structure-Π-Metric-Space =
    is-reflexive-structure-Π-Metric-Space ,
    is-symmetric-structure-Π-Metric-Space ,
    is-triangular-structure-Π-Metric-Space

  is-metric-structure-Π-Metric-Space :
    is-metric-Premetric structure-Π-Metric-Space
  is-metric-structure-Π-Metric-Space =
    is-pseudometric-structure-Π-Metric-Space ,
    is-local-structure-Π-Metric-Space

  Π-Metric-Space : Metric-Space (l ⊔ l1) (l ⊔ l2)
  pr1 Π-Metric-Space = type-Π-Metric-Space , structure-Π-Metric-Space
  pr2 Π-Metric-Space = is-metric-structure-Π-Metric-Space
```

## Properties

### The evaluation maps on a product metric space are short

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space l1 l2) (a : A)
  where

  is-short-ev-Π-Metric-Space :
    is-short-function-Metric-Space
      ( Π-Metric-Space A P)
      ( P a)
      ( ev a)
  is-short-ev-Π-Metric-Space ε x y H = H a

  short-ev-Π-Metric-Space :
    short-function-Metric-Space
      ( Π-Metric-Space A P)
      ( P a)
  short-ev-Π-Metric-Space = (ev a) , (is-short-ev-Π-Metric-Space)
```

### Dependent products of saturated metric spaces are saturated

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space l1 l2)
  (Π-saturated : (a : A) → is-saturated-Metric-Space (P a))
  where

  is-saturated-Π-is-saturated-Metric-Space :
    is-saturated-Metric-Space (Π-Metric-Space A P)
  is-saturated-Π-is-saturated-Metric-Space ε x y H a =
    Π-saturated a ε (x a) (y a) (λ d → H d a)
```

### The partial applications of a Cauchy approximation in a dependent product metric space are Cauchy approximations

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space (Π-Metric-Space A P))
  where

  ev-cauchy-approximation-Π-Metric-Space :
    (x : A) → cauchy-approximation-Metric-Space (P x)
  ev-cauchy-approximation-Π-Metric-Space x =
    map-short-function-cauchy-approximation-Metric-Space
      ( Π-Metric-Space A P)
      ( P x)
      ( short-ev-Π-Metric-Space A P x)
      ( f)
```

### A dependent map is the limit of a Cauchy approximation in a dependent product of metric spaces if and only if it is the pointwise limit of its partial applications

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space (Π-Metric-Space A P))
  (g : type-Π-Metric-Space A P)
  where

  is-pointwise-limit-is-limit-cauchy-approximation-Π-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( Π-Metric-Space A P)
      ( f)
      ( g) →
    (x : A) →
    is-limit-cauchy-approximation-Metric-Space
      ( P x)
      ( ev-cauchy-approximation-Π-Metric-Space A P f x)
      ( g x)
  is-pointwise-limit-is-limit-cauchy-approximation-Π-Metric-Space L x ε δ =
    L ε δ x

  is-limit-is-pointwise-limit-cauchy-approximation-Π-Metric-Space :
    ( (x : A) →
      is-limit-cauchy-approximation-Metric-Space
        ( P x)
        ( ev-cauchy-approximation-Π-Metric-Space A P f x)
        ( g x)) →
    is-limit-cauchy-approximation-Metric-Space
      ( Π-Metric-Space A P)
      ( f)
      ( g)
  is-limit-is-pointwise-limit-cauchy-approximation-Π-Metric-Space L ε δ x =
    L x ε δ
```

### A product of complete metric spaces is complete

```agda
module _
  {l l1 l2 : Level} (A : UU l) (P : A → Metric-Space l1 l2)
  (Π-complete : (x : A) → is-complete-Metric-Space (P x))
  where

  limit-cauchy-approximation-Π-is-complete-Metric-Space :
    cauchy-approximation-Metric-Space (Π-Metric-Space A P) →
    type-Π-Metric-Space A P
  limit-cauchy-approximation-Π-is-complete-Metric-Space u x =
    limit-cauchy-approximation-Complete-Metric-Space
      ( P x , Π-complete x)
      ( ev-cauchy-approximation-Π-Metric-Space A P u x)

  is-limit-limit-cauchy-approximation-Π-is-complete-Metric-Space :
    (u : cauchy-approximation-Metric-Space (Π-Metric-Space A P)) →
    is-limit-cauchy-approximation-Metric-Space
      ( Π-Metric-Space A P)
      ( u)
      ( limit-cauchy-approximation-Π-is-complete-Metric-Space u)
  is-limit-limit-cauchy-approximation-Π-is-complete-Metric-Space u ε δ x =
    is-limit-limit-cauchy-approximation-Complete-Metric-Space
      ( P x , Π-complete x)
      ( ev-cauchy-approximation-Π-Metric-Space A P u x)
      ( ε)
      ( δ)

  is-complete-Π-Metric-Space :
    is-complete-Metric-Space (Π-Metric-Space A P)
  is-complete-Π-Metric-Space u =
    limit-cauchy-approximation-Π-is-complete-Metric-Space u ,
    is-limit-limit-cauchy-approximation-Π-is-complete-Metric-Space u
```

### The complete product of complete metric spaces

```agda
module _
  {l l1 l2 : Level} (A : UU l) (C : A → Complete-Metric-Space l1 l2)
  where

  Π-Complete-Metric-Space : Complete-Metric-Space (l ⊔ l1) (l ⊔ l2)
  pr1 Π-Complete-Metric-Space =
    Π-Metric-Space A (metric-space-Complete-Metric-Space ∘ C)
  pr2 Π-Complete-Metric-Space =
    is-complete-Π-Metric-Space
      ( A)
      ( metric-space-Complete-Metric-Space ∘ C)
      ( is-complete-metric-space-Complete-Metric-Space ∘ C)
```
