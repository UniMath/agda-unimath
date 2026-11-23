# Rational neighborhood subtypes

```agda
module metric-spaces.rational-neighborhood-subtypes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "rational neighborhood subtype" Agda=Rational-Neighborhood-Subtype}}
is a type family of [subtypes](foundation.subtypes.md) indexed by the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md).

They are the underlying type of
[Cauchy filters](metric-spaces.cauchy-filters-pseudometric-spaces.md) on
[pseudometric spaces](metric-spaces.pseudometric-spaces.md).

## Definitions

### Rational neighborhood subtypes

```agda
module _
  {l1 : Level} (l : Level) (A : UU l1)
  where

  Rational-Neighborhood-Subtype : UU (l1 ⊔ lsuc l)
  Rational-Neighborhood-Subtype = ℚ⁺ → subtype l A

module _
  {l1 l : Level} {A : UU l1} (U : Rational-Neighborhood-Subtype l A)
  where

  is-in-Rational-Neighborhood-Subtype : ℚ⁺ → A → UU l
  is-in-Rational-Neighborhood-Subtype d x = type-Prop (U d x)

  is-prop-is-in-Rational-Neighborhood-Subtype :
    (d : ℚ⁺) (x : A) → is-prop (is-in-Rational-Neighborhood-Subtype d x)
  is-prop-is-in-Rational-Neighborhood-Subtype d x =
    is-prop-type-Prop (U d x)
```
