# Short functions between premetric spaces

```agda
module metric-spaces.short-functions-premetric-spaces where
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
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.premetric-spaces
```

</details>

## Idea

A funcion between [premetric spaces](metric-spaces.premetric-spaces.md) is
{{#concept "short" Disambiguation="function between premetric spaces" Agda=is-short-function-Premetric-Space}}
if it preserves it maps [`d`-close](metric-spaces.premetric-structures.md)
wlwmnts to `d`-close elements.

## Definitions

### The property of being a short function between premetric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : function-carrier-type-Premetric-Space A B)
  where

  is-short-function-prop-Premetric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-short-function-prop-Premetric-Space =
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
                  ( structure-Premetric-Space B d (f x) (f y)))))

  is-short-function-Premetric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-short-function-Premetric-Space =
    type-Prop is-short-function-prop-Premetric-Space

  is-prop-is-short-function-Premetric-Space :
    is-prop is-short-function-Premetric-Space
  is-prop-is-short-function-Premetric-Space =
    is-prop-type-Prop is-short-function-prop-Premetric-Space
```

### The type of short functions between premetric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  where

  short-function-Premetric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  short-function-Premetric-Space =
    type-subtype (is-short-function-prop-Premetric-Space A B)

module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : short-function-Premetric-Space A B)
  where

  map-short-function-Premetric-Space :
    function-carrier-type-Premetric-Space A B
  map-short-function-Premetric-Space = pr1 f

  is-short-map-short-function-Premetric-Space :
    is-short-function-Premetric-Space A B map-short-function-Premetric-Space
  is-short-map-short-function-Premetric-Space = pr2 f
```

## Properties

### Equality of short functions between premetric spaces is equivalent to homtopies between their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f g : short-function-Premetric-Space A B)
  where

  equiv-eq-htpy-map-short-function-Premetric-Space :
    ( f ＝ g) ≃
    ( map-short-function-Premetric-Space A B f ~
      map-short-function-Premetric-Space A B g)
  equiv-eq-htpy-map-short-function-Premetric-Space =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-short-function-prop-Premetric-Space A B) f g

  eq-htpy-map-short-function-Premetric-Space :
    ( map-short-function-Premetric-Space A B f ~
      map-short-function-Premetric-Space A B g) →
    ( f ＝ g)
  eq-htpy-map-short-function-Premetric-Space =
    map-inv-equiv equiv-eq-htpy-map-short-function-Premetric-Space
```

## References

- [Short maps](https://ncatlab.org/nlab/show/short+map) at $n$Lab
