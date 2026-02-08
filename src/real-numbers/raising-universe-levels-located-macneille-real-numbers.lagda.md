# Raising the universe levels of located MacNeille real numbers

```agda
module real-numbers.raising-universe-levels-located-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.embeddings
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.located-macneille-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.raising-universe-levels-lower-dedekind-real-numbers
open import real-numbers.raising-universe-levels-macneille-real-numbers
open import real-numbers.raising-universe-levels-upper-dedekind-real-numbers
open import real-numbers.rational-macneille-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-macneille-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

For every [universe](foundation.universe-levels.md) `𝒰` there is a type of
[located MacNeille real numbers](real-numbers.located-macneille-real-numbers.md)
`ℝ` relative to `𝒰`, `ℝ 𝒰`. Given a larger universe `𝒱`, then we may
{{#concept "raise" Disambiguation="a located MacNeille real number" Agda=raise-located-macneille-ℝ}}
a located MacNeille real number `x` from the universe `𝒰` to a
[similar](real-numbers.similarity-macneille-real-numbers.md) located MacNeille
real number in the universe `𝒱`.

## Definitions

### Raising located MacNeille real numbers

```agda
is-located-raise-macneille-real-ℚ :
  (l : Level) (q : ℚ) →
  is-located-macneille-ℝ (raise-macneille-real-ℚ l q)
is-located-raise-macneille-real-ℚ l q =
  pr2 (located-macneille-real-ℝ (raise-real-ℚ l q))

raise-located-macneille-real-ℚ :
  (l : Level) → ℚ → located-macneille-ℝ l
raise-located-macneille-real-ℚ l q =
  ( raise-macneille-real-ℚ l q ,
    is-located-raise-macneille-real-ℚ l q)

raise-zero-located-macneille-ℝ : (l : Level) → located-macneille-ℝ l
raise-zero-located-macneille-ℝ l =
  raise-located-macneille-real-ℚ l zero-ℚ

is-located-raise-located-macneille-ℝ :
  {l1 : Level} (l2 : Level) (x : located-macneille-ℝ l1) →
  is-located-macneille-ℝ (raise-macneille-ℝ l2 (pr1 x))
is-located-raise-located-macneille-ℝ l2 x p q p<q =
  map-disjunction map-raise map-raise (pr2 x p q p<q)

located-raise-macneille-ℝ :
  {l1 : Level} (l2 : Level) →
  located-macneille-ℝ l1 →
  located-macneille-ℝ (l1 ⊔ l2)
located-raise-macneille-ℝ l2 x =
  ( raise-macneille-ℝ l2 (pr1 x) ,
    is-located-raise-located-macneille-ℝ l2 x)
```
