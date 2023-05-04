# Dedekind real numbers

```agda
module real-numbers.dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.universe-levels

open import foundation-core.truncation-levels
```

</details>

## Idea

A **Dedekind cut** consists a pair `(L , U)` of subtypes of `ℚ`, satisfying the
following four conditions

1. _Inhabitedness_. Both `L` and `U` are inhabited subtypes of `ℚ`.
2. _Roundedness_. A rational number `q` is in `L` if and only if there exists
   `q < r` such that `r ∈ L`, and a rational number `r` is in `U` if and only if
   there exists `q < r` such that `q ∈ U`.
3. _Disjointness_. `L` and `U` are disjoint subsets of `ℚ`.
4. _Locatedness_. If `q < r` then `q ∈ L` or `r ∈ U`.

The type of Dedekind real numbers is the type of all dedekind cuts. The Dedekind
real numbers will be taken as the standard definition of the real numbers in the
`agda-unimath` library.

## Definition

### Dedekind cuts

```agda
is-dedekind-cut-Prop :
  {l : Level} → (ℚ → Prop l) → (ℚ → Prop l) → Prop l
is-dedekind-cut-Prop L U =
  prod-Prop
    ( prod-Prop (exists-Prop ℚ L) (exists-Prop ℚ U))
    ( prod-Prop
      ( prod-Prop
        ( Π-Prop ℚ
          ( λ q →
            iff-Prop
              ( L q)
              ( exists-Prop ℚ (λ r → prod-Prop (le-ℚ-Prop q r) (L r)))))
        ( Π-Prop ℚ
          ( λ r →
            iff-Prop
              ( U r)
              ( exists-Prop ℚ (λ q → prod-Prop (le-ℚ-Prop q r) (U q))))))
      ( prod-Prop
        ( Π-Prop ℚ (λ q → neg-Prop (prod-Prop (L q) (U q))))
        ( Π-Prop ℚ
          ( λ q →
            Π-Prop ℚ
              ( λ r →
                implication-Prop
                  ( le-ℚ-Prop q r)
                  ( disj-Prop (L q) (U r)))))))

is-dedekind-cut :
  {l : Level} → (ℚ → Prop l) → (ℚ → Prop l) → UU l
is-dedekind-cut L U = type-Prop (is-dedekind-cut-Prop L U)
```

### The Dedekind real numbers

```agda
ℝ : (l : Level) → UU (lsuc l)
ℝ l = Σ (ℚ → Prop l) (λ L → Σ (ℚ → Prop l) (is-dedekind-cut L))
```

### ℝ is a set

```agda
abstract

  is-set-ℝ : (l : Level) → is-set (ℝ l)
  is-set-ℝ l =
    is-set-Σ
      ( is-set-function-type (is-trunc-Truncated-Type neg-one-𝕋))
      ( λ x →
        ( is-set-Σ
          ( is-set-function-type (is-trunc-Truncated-Type neg-one-𝕋))
          ( λ y →
            ( is-set-is-prop
              ( is-prop-type-Prop
                ( is-dedekind-cut-Prop x y))))))

ℝ-Set : (l : Level) → Set (lsuc l)
pr1 (ℝ-Set l) = ℝ l
pr2 (ℝ-Set l) = is-set-ℝ l
```
