# Infima and suprema of families of real numbers

```agda
module real-numbers.infima-and-suprema-families-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.infima-families-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.subsets-real-numbers
open import real-numbers.suprema-families-real-numbers
```

</details>

## Idea

This file describes relationships between
[infima](real-numbers.infima-families-real-numbers.md) and
[suprema](real-numbers.suprema-families-real-numbers.md) of families and
[subsets](real-numbers.subsets-real-numbers.md) of the
[real numbers](real-numbers.dedekind-real-numbers.md).

## Properties

### If a set of real numbers has an infimum and a supremum, the infimum is less than or equal to the supremum

```agda
module _
  {l1 l2 l3 l4 : Level}
  (S : subset-ℝ l1 l2)
  (inf : ℝ l3)
  (is-inf : is-infimum-subset-ℝ S inf)
  (sup : ℝ l4)
  (is-sup : is-supremum-subset-ℝ S sup)
  where

  abstract
    leq-inf-sup-subset-ℝ : leq-ℝ inf sup
    leq-inf-sup-subset-ℝ =
      let open do-syntax-trunc-Prop (leq-prop-ℝ inf sup)
      in do
        (s , s∈S) ← is-inhabited-has-supremum-subset-ℝ S (sup , is-sup)
        transitive-leq-ℝ
          ( inf)
          ( s)
          ( sup)
          ( is-upper-bound-is-supremum-family-ℝ _ sup is-sup (s , s∈S))
          ( is-lower-bound-is-infimum-family-ℝ _ inf is-inf (s , s∈S))
```

### If a set of real numbers has an infimum `x` and a supremum `y`, it is a subset of a closed interval

```agda
abstract
  subset-closed-interval-has-inf-has-sup-subset-ℝ :
    {l1 l2 l3 l4 : Level} (S : subset-ℝ l1 l2) →
    has-infimum-subset-ℝ S l3 → has-supremum-subset-ℝ S l4 →
    Σ ( closed-interval-ℝ l3 l4)
      ( λ [a,b] → S ⊆ subtype-closed-interval-ℝ l2 [a,b])
  subset-closed-interval-has-inf-has-sup-subset-ℝ
    S (inf , is-inf) (sup , is-sup) =
      ( ( (inf , sup) ,
          leq-inf-sup-subset-ℝ S inf is-inf sup is-sup) ,
        ( λ s s∈S →
          ( is-lower-bound-is-infimum-family-ℝ _ inf is-inf (s , s∈S) ,
            is-upper-bound-is-supremum-family-ℝ _ sup is-sup (s , s∈S))))
```
