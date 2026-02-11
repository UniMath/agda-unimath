# Located metric spaces

```agda
module metric-spaces.located-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) is
{{#concept "located" Disambiguation="metric space" Agda=is-located-Metric-Space}}
if for any `x` and `y` in the metric space, and `δ ε : ℚ⁺` with `δ < ε`, merely
`x` and `y` are [not](foundation.negation.md) in a `δ`-neighborhood
[or](foundation.disjunction.md) `x` and `y` are in an `ε`-neighborhood.

If `x` and `y` are
[at bounded distance](metric-spaces.elements-at-bounded-distance-metric-spaces.md),
then this suffices to define a
[real number](real-numbers.dedekind-real-numbers.md) `d` such that for all
`ε : ℚ⁺`, `d ≤ ε` [if and only if](foundation.logical-equivalences.md) `x` and
`y` are in an `ε`-neighborhood of each other.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  is-located-prop-Metric-Space : Prop (l1 ⊔ l2)
  is-located-prop-Metric-Space =
    Π-Prop
      ( type-Metric-Space M)
      ( λ x →
        Π-Prop
          ( type-Metric-Space M)
          ( λ y →
            Π-Prop
              ( ℚ⁺)
              ( λ δ →
                Π-Prop
                  ( ℚ⁺)
                  ( λ ε →
                    hom-Prop
                      ( le-prop-ℚ⁺ δ ε)
                      ( ¬' (neighborhood-prop-Metric-Space M δ x y) ∨
                        neighborhood-prop-Metric-Space M ε x y)))))

  is-located-Metric-Space : UU (l1 ⊔ l2)
  is-located-Metric-Space = type-Prop is-located-prop-Metric-Space

Located-Metric-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Located-Metric-Space l1 l2 =
  type-subtype (is-located-prop-Metric-Space {l1} {l2})

module _
  {l1 l2 : Level} (X : Located-Metric-Space l1 l2)
  where

  metric-space-Located-Metric-Space : Metric-Space l1 l2
  metric-space-Located-Metric-Space = pr1 X

  type-Located-Metric-Space : UU l1
  type-Located-Metric-Space =
    type-Metric-Space metric-space-Located-Metric-Space

  neighborhood-prop-Located-Metric-Space :
    ℚ⁺ → Relation-Prop l2 type-Located-Metric-Space
  neighborhood-prop-Located-Metric-Space =
    neighborhood-prop-Metric-Space metric-space-Located-Metric-Space

  neighborhood-Located-Metric-Space : ℚ⁺ → Relation l2 type-Located-Metric-Space
  neighborhood-Located-Metric-Space =
    neighborhood-Metric-Space metric-space-Located-Metric-Space

  refl-neighborhood-Located-Metric-Space :
    (d : ℚ⁺) (x : type-Located-Metric-Space) →
    neighborhood-Located-Metric-Space d x x
  refl-neighborhood-Located-Metric-Space =
    refl-neighborhood-Metric-Space metric-space-Located-Metric-Space

  symmetric-neighborhood-Located-Metric-Space :
    (d : ℚ⁺) (x y : type-Located-Metric-Space) →
    neighborhood-Located-Metric-Space d x y →
    neighborhood-Located-Metric-Space d y x
  symmetric-neighborhood-Located-Metric-Space =
    symmetric-neighborhood-Metric-Space metric-space-Located-Metric-Space

  triangular-neighborhood-Located-Metric-Space :
    (x y z : type-Located-Metric-Space) (d₁ d₂ : ℚ⁺) →
    neighborhood-Located-Metric-Space d₂ y z →
    neighborhood-Located-Metric-Space d₁ x y →
    neighborhood-Located-Metric-Space (d₁ +ℚ⁺ d₂) x z
  triangular-neighborhood-Located-Metric-Space =
    triangular-neighborhood-Metric-Space metric-space-Located-Metric-Space

  monotonic-neighborhood-Located-Metric-Space :
    (x y : type-Located-Metric-Space) (d₁ d₂ : ℚ⁺) →
    le-ℚ⁺ d₁ d₂ →
    neighborhood-Located-Metric-Space d₁ x y →
    neighborhood-Located-Metric-Space d₂ x y
  monotonic-neighborhood-Located-Metric-Space =
    monotonic-neighborhood-Metric-Space metric-space-Located-Metric-Space

  is-located-Located-Metric-Space :
    is-located-Metric-Space metric-space-Located-Metric-Space
  is-located-Located-Metric-Space = pr2 X

  set-Located-Metric-Space : Set l1
  set-Located-Metric-Space = set-Metric-Space metric-space-Located-Metric-Space

subset-Located-Metric-Space :
  {l1 l2 : Level} (l3 : Level) (X : Located-Metric-Space l1 l2) →
  UU (l1 ⊔ lsuc l3)
subset-Located-Metric-Space l3 X =
  subset-Metric-Space l3 (metric-space-Located-Metric-Space X)
```

## Properties

### Located metric subspaces

```agda
module _
  {l1 l2 l3 : Level}
  (X : Located-Metric-Space l1 l2)
  (S : subset-Located-Metric-Space l3 X)
  where

  subspace-Located-Metric-Space : Metric-Space (l1 ⊔ l3) l2
  subspace-Located-Metric-Space =
    subspace-Metric-Space (metric-space-Located-Metric-Space X) S

  located-subspace-Located-Metric-Space : Located-Metric-Space (l1 ⊔ l3) l2
  located-subspace-Located-Metric-Space =
    ( subspace-Located-Metric-Space ,
      λ (x , _) (y , _) → is-located-Located-Metric-Space X x y)
```
