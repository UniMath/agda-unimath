# Similarity of positive real numbers

```agda
module real-numbers.similarity-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-equivalence-relations
open import foundation.large-similarity-relations
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

Two [positive](real-numbers.positive-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) are
{{#concept "similar" Disambiguation="positive real numbers" Agda=sim-ℝ⁺}} if
they are [similar](real-numbers.similarity-real-numbers.md) as real numbers.

## Definition

```agda
sim-prop-ℝ⁺ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → Prop (l1 ⊔ l2)
sim-prop-ℝ⁺ (x , _) (y , _) = sim-prop-ℝ x y

sim-ℝ⁺ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → UU (l1 ⊔ l2)
sim-ℝ⁺ (x , _) (y , _) = sim-ℝ x y
```

## Properties

### Similarity is a large equivalence relation

```agda
abstract
  refl-sim-ℝ⁺ : {l : Level} (x : ℝ⁺ l) → sim-ℝ⁺ x x
  refl-sim-ℝ⁺ (x , _) = refl-sim-ℝ x

  symmetric-sim-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) → sim-ℝ⁺ x y → sim-ℝ⁺ y x
  symmetric-sim-ℝ⁺ _ _ = symmetric-sim-ℝ

  transitive-sim-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) (z : ℝ⁺ l3) →
    sim-ℝ⁺ y z → sim-ℝ⁺ x y → sim-ℝ⁺ x z
  transitive-sim-ℝ⁺ (x , _) (y , _) (z , _) = transitive-sim-ℝ x y z

large-equivalence-relation-sim-ℝ⁺ : Large-Equivalence-Relation (_⊔_) ℝ⁺
large-equivalence-relation-sim-ℝ⁺ =
  make-Large-Equivalence-Relation
    ( sim-prop-ℝ⁺)
    ( refl-sim-ℝ⁺)
    ( symmetric-sim-ℝ⁺)
    ( transitive-sim-ℝ⁺)
```

### Similarity is a large similarity relation

```agda
abstract
  eq-sim-ℝ⁺ :
    {l : Level} (x y : ℝ⁺ l) → sim-ℝ⁺ x y → x ＝ y
  eq-sim-ℝ⁺ x y x~y = eq-ℝ⁺ x y (eq-sim-ℝ x~y)

large-similarity-relation-ℝ⁺ : Large-Similarity-Relation (_⊔_) ℝ⁺
large-similarity-relation-ℝ⁺ =
  make-Large-Similarity-Relation
    ( large-equivalence-relation-sim-ℝ⁺)
    ( eq-sim-ℝ⁺)
```

### Positive real numbers are similar to their raised universe level counterparts

```agda
abstract
  sim-raise-ℝ⁺ : {l0 : Level} (l : Level) (x : ℝ⁺ l0) → sim-ℝ⁺ x (raise-ℝ⁺ l x)
  sim-raise-ℝ⁺ l (x , _) = sim-raise-ℝ l x
```

### The cumulative large set of positive real numbers

```agda
cumulative-large-set-ℝ⁺ : Cumulative-Large-Set lsuc (_⊔_)
cumulative-large-set-ℝ⁺ =
  λ where
    .type-Cumulative-Large-Set →
      ℝ⁺
    .large-similarity-relation-Cumulative-Large-Set →
      large-similarity-relation-ℝ⁺
    .raise-Cumulative-Large-Set →
      raise-ℝ⁺
    .sim-raise-Cumulative-Large-Set →
      sim-raise-ℝ⁺
```
