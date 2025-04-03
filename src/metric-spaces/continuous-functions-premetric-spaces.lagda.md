# Continuous functions between premetric spaces

```agda
module metric-spaces.continuous-functions-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.premetric-spaces
```

</details>

## Idea

A function `f` between [premetric spaces](metric-spaces.premetric-spaces.md) `X`
and `Y` is
{{#concept "continuous" Disambiguation="function between premetric spaces at a point" WDID=Q170058 WD="continuous function" Agda=is-continuous-at-point-Premetric-Space}}
at a point `x` if there exists a function `m : ℚ⁺ → ℚ⁺` such that whenever `x'`
is in an `m ε`-neighborhood of `x`, `f x'` is in an `ε`-neighborhood of `f x`.
`m` is called a modulus of continuity of `f` at `x`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Premetric-Space l1 l2) (Y : Premetric-Space l3 l4)
  (f : map-type-Premetric-Space X Y)
  where

  is-modulus-of-continuity-at-point-prop-Premetric-Space :
    (x : type-Premetric-Space X) → (ℚ⁺ → ℚ⁺) → Prop (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-continuity-at-point-prop-Premetric-Space x m =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( type-Premetric-Space X)
          ( λ x' →
            structure-Premetric-Space X (m ε) x x' ⇒
            structure-Premetric-Space Y ε (f x) (f x')))

  is-modulus-of-continuity-at-point-Premetric-Space :
    (x : type-Premetric-Space X) → UU (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-continuity-at-point-Premetric-Space x =
    type-subtype (is-modulus-of-continuity-at-point-prop-Premetric-Space x)

  is-continuous-at-point-prop-Premetric-Space :
    (x : type-Premetric-Space X) → Prop (l1 ⊔ l2 ⊔ l4)
  is-continuous-at-point-prop-Premetric-Space x =
    is-inhabited-subtype-Prop
      (is-modulus-of-continuity-at-point-prop-Premetric-Space x)

  is-continuous-at-point-Premetric-Space :
    (x : type-Premetric-Space X) → UU (l1 ⊔ l2 ⊔ l4)
  is-continuous-at-point-Premetric-Space x =
    type-Prop (is-continuous-at-point-prop-Premetric-Space x)
```
