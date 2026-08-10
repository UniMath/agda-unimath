# Limits of Cauchy approximations in metric spaces

```agda
module metric-spaces.limits-of-cauchy-approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

A [Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md)
`f : ℚ⁺ → A` in a [metric space](metric-spaces.metric-spaces.md) `A` has a
{{#concept "limit" Disambiguation="of a Cauchy approximation in a metric space" Agda=is-limit-cauchy-approximation-Metric-Space}}
`x : A` if `f ε` is near `x` for small `ε : ℚ⁺`. More precisely, `f` has a limit
if `f ε` is in a
`ε + δ`-[neighborhood](metric-spaces.rational-neighborhood-relations.md) of `x`
for all
[positive rationals](elementary-number-theory.positive-rational-numbers.md) `ε`
and `δ`.

These are
[limits](metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.md)
in the underlying [pseudometric space](metric-spaces.pseudometric-spaces.md)
but, because metric spaces are
[extensional](metric-spaces.extensionality-pseudometric-spaces.md), all limits
of a Cauchy approximation in a metric space are equal.

## Definitions

### The property of having a limit in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space A)
  where

  is-limit-cauchy-approximation-prop-Metric-Space :
    type-Metric-Space A → Prop l2
  is-limit-cauchy-approximation-prop-Metric-Space =
    is-limit-cauchy-approximation-prop-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( f)

  is-limit-cauchy-approximation-Metric-Space :
    type-Metric-Space A → UU l2
  is-limit-cauchy-approximation-Metric-Space =
    type-Prop ∘ is-limit-cauchy-approximation-prop-Metric-Space
```

## Properties

### Saturation of the limit

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space A)
  (x : type-Metric-Space A)
  where

  abstract
    saturated-is-limit-cauchy-approximation-Metric-Space :
      is-limit-cauchy-approximation-Metric-Space A f x →
      (ε : ℚ⁺) →
      neighborhood-Metric-Space A ε
        ( map-cauchy-approximation-Metric-Space A f ε)
        ( x)
    saturated-is-limit-cauchy-approximation-Metric-Space =
      saturated-is-limit-cauchy-approximation-Pseudometric-Space
        ( pseudometric-Metric-Space A)
        ( f)
        ( x)
```

### Limits in a metric space are unique

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space A)
  (x y : type-Metric-Space A)
  where

  all-sim-is-limit-cauchy-approximation-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space A f x →
    is-limit-cauchy-approximation-Metric-Space A f y →
    sim-Metric-Space A x y
  all-sim-is-limit-cauchy-approximation-Metric-Space =
    all-sim-is-limit-cauchy-approximation-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( f)
      ( x)
      ( y)

  all-eq-is-limit-cauchy-approximation-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space A f x →
    is-limit-cauchy-approximation-Metric-Space A f y →
    x ＝ y
  all-eq-is-limit-cauchy-approximation-Metric-Space lim-x lim-y =
    eq-sim-Metric-Space
      ( A)
      ( x)
      ( y)
      ( all-sim-is-limit-cauchy-approximation-Metric-Space lim-x lim-y)
```

### The value of a constant Cauchy approximation is its limit

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (x : type-Metric-Space A)
  where

  is-limit-const-cauchy-approximation-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( A)
      ( const-cauchy-approximation-Metric-Space A x)
      ( x)
  is-limit-const-cauchy-approximation-Metric-Space =
    is-limit-const-cauchy-approximation-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( x)
```

### Convergent Cauchy approximations are similar to constant Cauchy approximations in the Cauchy pseudocompletion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : cauchy-approximation-Metric-Space M)
  (x : type-Metric-Space M)
  where abstract

  sim-const-is-limit-cauchy-approximation-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space M u x →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( u)
      ( const-cauchy-approximation-Metric-Space M x)
  sim-const-is-limit-cauchy-approximation-Metric-Space H d α β =
    monotonic-neighborhood-Metric-Space
      ( M)
      ( map-cauchy-approximation-Metric-Space M u α)
      ( x)
      ( α +ℚ⁺ β)
      ( α +ℚ⁺ β +ℚ⁺ d)
      ( le-left-add-ℚ⁺ (α +ℚ⁺ β) d)
      ( H α β)

  is-limit-sim-const-cauchy-approximation-Metric-Space :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( u)
      ( const-cauchy-approximation-Metric-Space M x) →
    is-limit-cauchy-approximation-Metric-Space M u x
  is-limit-sim-const-cauchy-approximation-Metric-Space H α β =
    saturated-neighborhood-Metric-Space
      ( M)
      ( α +ℚ⁺ β)
      ( map-cauchy-approximation-Metric-Space M u α)
      ( x)
      ( λ d → H d α β)
```

### Cauchy approximations with the same limit are similar in the Cauchy pseudocompletion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u v : cauchy-approximation-Metric-Space M)
  (x : type-Metric-Space M)
  (is-limit-u-x : is-limit-cauchy-approximation-Metric-Space M u x)
  (is-limit-v-x : is-limit-cauchy-approximation-Metric-Space M v x)
  where abstract

  sim-is-limit-cauchy-approximation-Metric-Space :
    sim-cauchy-pseudocompletion-Metric-Space M u v
  sim-is-limit-cauchy-approximation-Metric-Space =
    transitive-sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( u)
      ( const-cauchy-approximation-Metric-Space M x)
      ( v)
      ( symmetric-sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( v)
        ( const-cauchy-approximation-Metric-Space M x)
        ( sim-const-is-limit-cauchy-approximation-Metric-Space M
          ( v)
          ( x)
          ( is-limit-v-x)))
      ( sim-const-is-limit-cauchy-approximation-Metric-Space M u x is-limit-u-x)
```

### If two Cauchy approximations are similar and have limits, the limits are equal

```agda
module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  (u v : cauchy-approximation-Metric-Space M)
  (u~v : sim-cauchy-pseudocompletion-Metric-Space M u v)
  (x y : type-Metric-Space M)
  (is-lim-u-x : is-limit-cauchy-approximation-Metric-Space M u x)
  (is-lim-v-y : is-limit-cauchy-approximation-Metric-Space M v y)
  where abstract

  eq-limit-sim-cauchy-pseudocompletion-Metric-Space : x ＝ y
  eq-limit-sim-cauchy-pseudocompletion-Metric-Space =
    all-eq-is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( v)
      ( x)
      ( y)
      ( has-same-limit-sim-cauchy-approximation-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( u)
        ( v)
        ( x)
        ( u~v)
        ( is-lim-u-x))
      ( is-lim-v-y)
```

### Cauchy approximations with limits are similar if and only if the limits are equal

```agda
module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  (u v : cauchy-approximation-Metric-Space M)
  {x y : type-Metric-Space M}
  (is-lim-u-x : is-limit-cauchy-approximation-Metric-Space M u x)
  (is-lim-v-y : is-limit-cauchy-approximation-Metric-Space M v y)
  where

  eq-limit-iff-sim-cauchy-pseudocompletion-Metric-Space :
    sim-cauchy-pseudocompletion-Metric-Space M u v ↔ (x ＝ y)
  pr1 eq-limit-iff-sim-cauchy-pseudocompletion-Metric-Space u~v =
    eq-limit-sim-cauchy-pseudocompletion-Metric-Space M
      ( u)
      ( v)
      ( u~v)
      ( x)
      ( y)
      ( is-lim-u-x)
      ( is-lim-v-y)
  pr2 eq-limit-iff-sim-cauchy-pseudocompletion-Metric-Space refl =
    sim-is-limit-cauchy-approximation-Metric-Space M u v x is-lim-u-x is-lim-v-y
```

### Homotopic Cauchy approximations have the same limits

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f g : cauchy-approximation-Metric-Space A)
  (x : type-Metric-Space A)
  (f~g : htpy-map-cauchy-approximation-Metric-Space A f g)
  where abstract

  is-limit-htpy-map-cauchy-approximation-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space A f x →
    is-limit-cauchy-approximation-Metric-Space A g x
  is-limit-htpy-map-cauchy-approximation-Metric-Space =
    is-limit-htpy-map-cauchy-approximation-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( f)
      ( g)
      ( x)
      ( f~g)
```

### If two Cauchy approximations have limits, they are in a `d`-neighborhood in the Cauchy pseudocompletion if and only if their limits are in a `d`-neighborhood

```agda
module _
  {l1 l2 : Level}
  (X : Metric-Space l1 l2)
  (d : ℚ⁺)
  (f g : cauchy-approximation-Metric-Space X)
  (x y : type-Metric-Space X)
  (is-lim-f-x : is-limit-cauchy-approximation-Metric-Space X f x)
  (is-lim-g-y : is-limit-cauchy-approximation-Metric-Space X g y)
  where

  abstract
    same-neighborhoods-limits-cauchy-pseudocompletion-Metric-Space :
      neighborhood-cauchy-pseudocompletion-Metric-Space X d f g ↔
      neighborhood-Metric-Space X d x y
    same-neighborhoods-limits-cauchy-pseudocompletion-Metric-Space =
      logical-equivalence-reasoning
        neighborhood-cauchy-pseudocompletion-Metric-Space X d f g
        ↔ neighborhood-cauchy-pseudocompletion-Metric-Space X
            ( d)
            ( const-cauchy-approximation-Metric-Space X x)
            ( const-cauchy-approximation-Metric-Space X y)
          by
            preserves-and-reflects-neighborhoods-sim-Pseudometric-Space
              ( cauchy-pseudocompletion-Metric-Space X)
              { x = f}
              { x' = const-cauchy-approximation-Metric-Space X x}
              { y = g}
              { y' = const-cauchy-approximation-Metric-Space X y}
              ( sim-const-is-limit-cauchy-approximation-Metric-Space X
                ( f)
                ( x)
                ( is-lim-f-x))
              ( sim-const-is-limit-cauchy-approximation-Metric-Space
                ( X)
                ( g)
                ( y)
                ( is-lim-g-y))
              ( d)
        ↔ neighborhood-Metric-Space X d x y
          by
            inv-iff
              ( is-isometry-map-unit-cauchy-pseudocompletion-Metric-Space
                ( X)
                ( d)
                ( x)
                ( y))

  preserves-neighborhoods-limits-cauchy-approximation-Metric-Space :
    neighborhood-cauchy-pseudocompletion-Metric-Space X d f g →
    neighborhood-Metric-Space X d x y
  preserves-neighborhoods-limits-cauchy-approximation-Metric-Space =
    forward-implication
      ( same-neighborhoods-limits-cauchy-pseudocompletion-Metric-Space)

  reflects-neighborhoods-limits-cauchy-approximation-Metric-Space :
    neighborhood-Metric-Space X d x y →
    neighborhood-cauchy-pseudocompletion-Metric-Space X d f g
  reflects-neighborhoods-limits-cauchy-approximation-Metric-Space =
    backward-implication
      ( same-neighborhoods-limits-cauchy-pseudocompletion-Metric-Space)
```

## See also

- [Convergent cauchy approximations](metric-spaces.convergent-cauchy-approximations-metric-spaces.md)
  are Cauchy approximations with a limit.

## References

Our definition of limit of Cauchy approximation follows Definition 11.2.10 of
{{#cite UF13}}.

{{#bibliography}}
