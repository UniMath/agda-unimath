# Premetric spaces

```agda
module metric-spaces.premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.discrete-premetric-structures
open import metric-spaces.premetric-structures
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

A {{#concept "premetric space" Agda=Premetric-Space}} is a type
[equipped](foundation.structure.md) with a
[premetric](metric-spaces.premetric-structures.md).

## Definitions

### The type of premetric spaces

```agda
Premetric-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Premetric-Space l1 l2 = Σ (UU l1) (Premetric l2)

module _
  {l1 l2 : Level} (M : Premetric-Space l1 l2)
  where

  type-Premetric-Space : UU l1
  type-Premetric-Space = pr1 M

  structure-Premetric-Space : Premetric l2 type-Premetric-Space
  structure-Premetric-Space = pr2 M

  neighborhood-Premetric-Space :
    ℚ⁺ → type-Premetric-Space → type-Premetric-Space → UU l2
  neighborhood-Premetric-Space =
    neighborhood-Premetric structure-Premetric-Space

  is-prop-neighborhood-Premetric-Space :
    (d : ℚ⁺) (x y : type-Premetric-Space) →
    is-prop (neighborhood-Premetric-Space d x y)
  is-prop-neighborhood-Premetric-Space =
    is-prop-neighborhood-Premetric structure-Premetric-Space

  is-upper-bound-dist-Premetric-Space :
    (x y : type-Premetric-Space) (d : ℚ⁺) → UU l2
  is-upper-bound-dist-Premetric-Space =
    is-upper-bound-dist-Premetric structure-Premetric-Space

  is-prop-is-upper-bound-dist-Premetric-Space :
    (x y : type-Premetric-Space) (d : ℚ⁺) →
    is-prop (is-upper-bound-dist-Premetric-Space x y d)
  is-prop-is-upper-bound-dist-Premetric-Space =
    is-prop-is-upper-bound-dist-Premetric structure-Premetric-Space

  is-indistinguishable-prop-Premetric-Space :
    (x y : type-Premetric-Space) → Prop l2
  is-indistinguishable-prop-Premetric-Space =
    is-indistinguishable-prop-Premetric structure-Premetric-Space

  is-indistinguishable-Premetric-Space :
    (x y : type-Premetric-Space) → UU l2
  is-indistinguishable-Premetric-Space =
    is-indistinguishable-Premetric structure-Premetric-Space

  is-prop-is-indistinguishable-Premetric-Space :
    (x y : type-Premetric-Space) →
    is-prop (is-indistinguishable-Premetric-Space x y)
  is-prop-is-indistinguishable-Premetric-Space =
    is-prop-is-indistinguishable-Premetric structure-Premetric-Space
```

### The type of functions between premetric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  where

  map-type-Premetric-Space : UU (l1 ⊔ l1')
  map-type-Premetric-Space =
    type-Premetric-Space A → type-Premetric-Space B
```

### The identity map on a premetric space

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  where

  id-Premetric-Space : map-type-Premetric-Space A A
  id-Premetric-Space = id
```

### Any type is a discrete premetric space

```agda
module _
  {l : Level} (A : UU l)
  where

  discrete-Premetric-Space : Premetric-Space l l
  discrete-Premetric-Space = A , premetric-discrete-Premetric A
```
