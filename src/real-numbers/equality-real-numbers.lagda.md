# Equality of real numbers

```agda
module real-numbers.equality-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.double-negation
open import foundation.double-negation-stable-equality
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

We record that [equality](foundation-core.identity-types.md) and
[similarity](real-numbers.similarity-real-numbers.md) of
[Dedekind real numbers](real-numbers.dedekind-real-numbers.md) is
[double negation stable](foundation.double-negation-stable-equality.md).

## Properties

### Similarity of Dedekind real numbers is double negation stable

```agda
module _
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2}
  where abstract

  double-negation-elim-sim-ℝ : ¬¬ (x ~ℝ y) → x ~ℝ y
  double-negation-elim-sim-ℝ H =
    sim-antisymmetric-leq-ℝ x y
      ( double-negation-elim-leq-ℝ x y (map-double-negation leq-sim-ℝ H))
      ( double-negation-elim-leq-ℝ y x (map-double-negation leq-sim-ℝ' H))
```

### Equality of Dedekind real numbers is double negation stable

```agda
module _
  {l : Level} {x y : ℝ l}
  where abstract

  double-negation-elim-eq-ℝ : ¬¬ (x ＝ y) → x ＝ y
  double-negation-elim-eq-ℝ H =
    eq-sim-ℝ (double-negation-elim-sim-ℝ (map-double-negation sim-eq-ℝ H))
```

### The Dedekind real numbers form a set

This fact is already demonstrated in
[`real-numbers.dedekind-real-numbers`](real-numbers.dedekind-real-numbers.md),
but we give a second proof using the fact that equality satisfies double
negation elimination.

```agda
is-set-ℝ' : {l : Level} → is-set (ℝ l)
is-set-ℝ' =
  is-set-has-double-negation-stable-equality (λ x y → double-negation-elim-eq-ℝ)
```
