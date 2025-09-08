# Totally bounded metric spaces

```agda
module metric-spaces.totally-bounded-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.images-isometries-metric-spaces
open import metric-spaces.images-metric-spaces
open import metric-spaces.images-short-functions-metric-spaces
open import metric-spaces.images-uniformly-continuous-functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.nets-metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) is
{{#concept "totally bounded" disambiguation="metric space" WDID=Q1362228 WD="totally bounded space" Agda=is-totally-bounded-Metric-Space}}
if for every `ε : ℚ⁺`, it has an `ε`-[net](metric-spaces.nets-metric-spaces.md).

## Definition

### The property of a space being totally bounded

```agda
module _
  {l1 l2 : Level} (l3 : Level) (X : Metric-Space l1 l2)
  where

  modulus-of-total-boundedness-Metric-Space : UU (l1 ⊔ l2 ⊔ lsuc l3)
  modulus-of-total-boundedness-Metric-Space =
    (ε : ℚ⁺) → net-Metric-Space l3 X ε

  is-totally-bounded-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-totally-bounded-prop-Metric-Space =
    trunc-Prop modulus-of-total-boundedness-Metric-Space

  is-totally-bounded-Metric-Space : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-totally-bounded-Metric-Space =
    type-Prop is-totally-bounded-prop-Metric-Space
```

### Totally bounded metric spaces

```agda
totally-bounded-Metric-Space :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
totally-bounded-Metric-Space l1 l2 l3 =
  Σ (Metric-Space l1 l2) (is-totally-bounded-Metric-Space l3)

module _
  {l1 l2 l3 : Level} (M : totally-bounded-Metric-Space l1 l2 l3)
  where

  metric-space-totally-bounded-Metric-Space : Metric-Space l1 l2
  metric-space-totally-bounded-Metric-Space = pr1 M

  is-totally-bounded-metric-space-totally-bounded-Metric-Space :
    is-totally-bounded-Metric-Space l3 metric-space-totally-bounded-Metric-Space
  is-totally-bounded-metric-space-totally-bounded-Metric-Space =
    pr2 M
```

## Properties

### The image of a totally bounded metric space under a uniformly continuous function is totally bounded

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (μX : modulus-of-total-boundedness-Metric-Space l5 X)
  (f : type-function-Metric-Space X Y)
  {μf : ℚ⁺ → ℚ⁺}
  (is-muc-μf : is-modulus-of-uniform-continuity-function-Metric-Space X Y f μf)
  where

  modulus-of-total-boundedness-im-modulated-uniformly-continuous-function-Metric-Space :
    modulus-of-total-boundedness-Metric-Space
      ( l1 ⊔ l3 ⊔ l5)
      ( im-Metric-Space X Y f)
  modulus-of-total-boundedness-im-modulated-uniformly-continuous-function-Metric-Space
    ε =
      net-im-uniformly-continuous-function-net-Metric-Space X Y f
        ( is-muc-μf)
        ( ε)
        ( μX (μf ε))

module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (tbX : is-totally-bounded-Metric-Space l5 X)
  (f : uniformly-continuous-function-Metric-Space X Y)
  where

  abstract
    is-totally-bounded-im-uniformly-continuous-function-is-totally-bounded-Metric-Space :
      is-totally-bounded-Metric-Space
        ( l1 ⊔ l3 ⊔ l5)
        ( im-uniformly-continuous-function-Metric-Space X Y f)
    is-totally-bounded-im-uniformly-continuous-function-is-totally-bounded-Metric-Space =
      let
        open
          do-syntax-trunc-Prop
            ( is-totally-bounded-prop-Metric-Space
              ( l1 ⊔ l3 ⊔ l5)
              ( im-uniformly-continuous-function-Metric-Space X Y f))
      in do
        (_ , μf) ←
          is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space
            ( X)
            ( Y)
            ( f)
        μX ← tbX
        unit-trunc-Prop
          ( modulus-of-total-boundedness-im-modulated-uniformly-continuous-function-Metric-Space
            ( X)
            ( Y)
            ( μX)
            ( map-uniformly-continuous-function-Metric-Space X Y f)
            ( μf))
```

### The image of a totally bounded metric space under a short function is totally bounded

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (tbX : is-totally-bounded-Metric-Space l5 X)
  (f : short-function-Metric-Space X Y)
  where

  abstract
    is-totally-bounded-im-short-function-is-totally-bounded-Metric-Space :
      is-totally-bounded-Metric-Space
        ( l1 ⊔ l3 ⊔ l5)
        ( im-short-function-Metric-Space X Y f)
    is-totally-bounded-im-short-function-is-totally-bounded-Metric-Space =
      is-totally-bounded-im-uniformly-continuous-function-is-totally-bounded-Metric-Space
        ( X)
        ( Y)
        ( tbX)
        ( uniformly-continuous-short-function-Metric-Space X Y f)
```

### The image of a totally bounded metric space under an isometry is totally bounded

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (tbX : is-totally-bounded-Metric-Space l5 X)
  (f : isometry-Metric-Space X Y)
  where

  abstract
    is-totally-bounded-im-isometry-is-totally-bounded-Metric-Space :
      is-totally-bounded-Metric-Space
        ( l1 ⊔ l3 ⊔ l5)
        ( im-isometry-Metric-Space X Y f)
    is-totally-bounded-im-isometry-is-totally-bounded-Metric-Space =
      is-totally-bounded-im-short-function-is-totally-bounded-Metric-Space
        ( X)
        ( Y)
        ( tbX)
        ( short-isometry-Metric-Space X Y f)
```

### Total boundedness is preserved by isometric equivalences

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (tbX : is-totally-bounded-Metric-Space l5 X)
  (f : isometric-equiv-Metric-Space X Y)
  where

  abstract
    preserves-is-totally-bounded-isometric-equiv-Metric-Space :
      is-totally-bounded-Metric-Space (l1 ⊔ l3 ⊔ l5) Y
    preserves-is-totally-bounded-isometric-equiv-Metric-Space =
      map-is-inhabited
        ( λ μX ε → net-im-isometric-equiv-net-Metric-Space X Y f ε (μX ε))
        ( tbX)
```
