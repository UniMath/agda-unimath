# Uniformly continuous functions between premetric spaces

```agda
module metric-spaces.uniformly-continuous-functions-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.continuous-functions-premetric-spaces
open import metric-spaces.premetric-spaces
```

</details>

## Idea

A function `f` between [premetric spaces](metric-spaces.premetric-spaces.md) `X`
and `Y` is
{{#concept "uniformly continuous" Disambiguation="function between metric spaces" WDID=Q741865 WD="uniform continuity" Agda=is-uniformly-continuous-map-Premetric-Space}}
if there exists a function `m : ℚ⁺ → ℚ⁺` such that for any `x : X`, whenever
`x'` is in an `m ε`-neighborhood of `x`, `f x'` is in an `ε`-neighborhood of
`f x`. The function `m` is called a modulus of uniform continuity of `f`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Premetric-Space l1 l2) (Y : Premetric-Space l3 l4)
  (f : map-type-Premetric-Space X Y)
  where

  is-modulus-of-uniform-continuity-prop-Premetric-Space :
    (ℚ⁺ → ℚ⁺) → Prop (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-uniform-continuity-prop-Premetric-Space m =
    Π-Prop
      ( type-Premetric-Space X)
      ( λ x → is-modulus-of-continuity-at-point-prop-Premetric-Space X Y f x m)

  is-uniformly-continuous-map-prop-Premetric-Space : Prop (l1 ⊔ l2 ⊔ l4)
  is-uniformly-continuous-map-prop-Premetric-Space =
    is-inhabited-subtype-Prop
      ( is-modulus-of-uniform-continuity-prop-Premetric-Space)

  is-uniformly-continuous-map-Premetric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-uniformly-continuous-map-Premetric-Space =
    type-Prop is-uniformly-continuous-map-prop-Premetric-Space

  is-continuous-at-point-is-uniformly-continuous-map-Premetric-Space :
    is-uniformly-continuous-map-Premetric-Space → (x : type-Premetric-Space X) →
    is-continuous-at-point-Premetric-Space X Y f x
  is-continuous-at-point-is-uniformly-continuous-map-Premetric-Space H x =
    do
      m , is-modulus-uniform-m ← H
      intro-exists m (is-modulus-uniform-m x)
    where
      open
        do-syntax-trunc-Prop
          ( is-continuous-at-point-prop-Premetric-Space X Y f x)
```

## Properties

### The identity function is uniformly continuous

```agda
module _
  {l1 l2 : Level} (X : Premetric-Space l1 l2)
  where

  is-uniformly-continuous-map-id-Premetric-Space :
    is-uniformly-continuous-map-Premetric-Space X X id
  is-uniformly-continuous-map-id-Premetric-Space =
    intro-exists id (λ _ _ _ → id)
```

### The composition of uniformly continuous functions is uniformly continuous

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : Premetric-Space l1 l2)
  (Y : Premetric-Space l3 l4)
  (Z : Premetric-Space l5 l6)
  (f : map-type-Premetric-Space Y Z) (g : map-type-Premetric-Space X Y)
  where

  is-uniformly-continuous-map-comp-Premetric-Space :
    is-uniformly-continuous-map-Premetric-Space Y Z f →
    is-uniformly-continuous-map-Premetric-Space X Y g →
    is-uniformly-continuous-map-Premetric-Space X Z (f ∘ g)
  is-uniformly-continuous-map-comp-Premetric-Space H K =
    do
      mf , is-modulus-uniform-mf ← H
      mg , is-modulus-uniform-mg ← K
      intro-exists
        ( mg ∘ mf)
        ( λ x ε x' →
          is-modulus-uniform-mf (g x) ε (g x') ∘
          is-modulus-uniform-mg x (mf ε) x')
    where
      open
        do-syntax-trunc-Prop
          ( is-uniformly-continuous-map-prop-Premetric-Space X Z (f ∘ g))
```
