# Lipschitz functions between premetric spaces

```agda
module metric-spaces.lipschitz-functions-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.isometries-premetric-spaces
open import metric-spaces.premetric-spaces
open import metric-spaces.short-functions-premetric-spaces
open import metric-spaces.uniformly-continuous-functions-premetric-spaces
```

</details>

## Idea

A map `f : A → B` between [premetric spaces](metric-spaces.premetric-spaces.md)
is a {{#concept "Lipschitz function" Disambiguation="between premetric spaces"}}
if there exists some `α : ℚ⁺` such that for any `x y :A`, if `d` is an upper
bound of the distance between `x` and `y` in `A`, `α d` is an upper bound on the
distance between `f x` and `f y` in `B`.

## Definitions

### The property of being a Lipschitz constant of a map between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : map-type-Premetric-Space A B)
  where

  is-lipschitz-constant-prop-function-Premetric-Space :
    ℚ⁺ → Prop (l1 ⊔ l2 ⊔ l2')
  is-lipschitz-constant-prop-function-Premetric-Space α =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( type-Premetric-Space A)
          ( λ x →
            Π-Prop
            ( type-Premetric-Space A)
            ( λ y →
              hom-Prop
                ( structure-Premetric-Space A d x y)
                ( structure-Premetric-Space B (α *ℚ⁺ d) (f x) (f y)))))

  is-lipschitz-constant-function-Premetric-Space : ℚ⁺ → UU (l1 ⊔ l2 ⊔ l2')
  is-lipschitz-constant-function-Premetric-Space α =
    type-Prop (is-lipschitz-constant-prop-function-Premetric-Space α)

  is-prop-is-lipschitz-constant-function-Premetric-Space :
    (α : ℚ⁺) →
    is-prop (is-lipschitz-constant-function-Premetric-Space α)
  is-prop-is-lipschitz-constant-function-Premetric-Space α =
    is-prop-type-Prop (is-lipschitz-constant-prop-function-Premetric-Space α)
```

### The property of being a Lipschitz function

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  where

  is-lipschitz-prop-function-Premetric-Space :
    map-type-Premetric-Space A B → Prop (l1 ⊔ l2 ⊔ l2')
  is-lipschitz-prop-function-Premetric-Space f =
    is-inhabited-subtype-Prop
      (is-lipschitz-constant-prop-function-Premetric-Space A B f)

  is-lipschitz-function-Premetric-Space :
    map-type-Premetric-Space A B → UU (l1 ⊔ l2 ⊔ l2')
  is-lipschitz-function-Premetric-Space f =
    type-Prop (is-lipschitz-prop-function-Premetric-Space f)

  is-prop-is-lipschitz-function-Premetric-Space :
    (f : map-type-Premetric-Space A B) →
    is-prop (is-lipschitz-function-Premetric-Space f)
  is-prop-is-lipschitz-function-Premetric-Space f =
    is-prop-type-Prop (is-lipschitz-prop-function-Premetric-Space f)
```

## Properties

### Short functions are Lipschitz functions with Lipschitz constant equal to 1

TODO

### Lipschitz functions are uniformly continuous

TODO

### The composition of Lipschitz functions is Lipschitz

TODO

## External links

- [Lipschitz maps](https://en.wikipedia.org/wiki/Lipschitz_continuity) at
  Wikipedia
