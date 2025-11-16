# Similarity of complex numbers

```agda
module complex-numbers.similarity-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-equivalence-relations
open import foundation.large-similarity-relations
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

Two [complex numbers](complex-numbers.complex-numbers.md) are
{{#concept "similar" Disambiguation="complex numbers" Agda=sim-ℂ}} if their
[real](real-numbers.dedekind-real-numbers.md) and imaginary parts are
[similar](real-numbers.similarity-real-numbers.md).

## Definition

```agda
sim-prop-ℂ : {l1 l2 : Level} → ℂ l1 → ℂ l2 → Prop (l1 ⊔ l2)
sim-prop-ℂ (a , b) (c , d) = sim-prop-ℝ a c ∧ sim-prop-ℝ b d

sim-ℂ : {l1 l2 : Level} → ℂ l1 → ℂ l2 → UU (l1 ⊔ l2)
sim-ℂ a+bi c+di = type-Prop (sim-prop-ℂ a+bi c+di)
```

## Properties

### Similarity is reflexive

```agda
abstract
  refl-sim-ℂ : {l : Level} (z : ℂ l) → sim-ℂ z z
  refl-sim-ℂ (a , b) = (refl-sim-ℝ a , refl-sim-ℝ b)

  sim-eq-ℂ : {l : Level} {z w : ℂ l} → z ＝ w → sim-ℂ z w
  sim-eq-ℂ {z = z} refl = refl-sim-ℂ z
```

### Similarity is symmetric

```agda
abstract
  symmetric-sim-ℂ :
    {l1 l2 : Level} {x : ℂ l1} {y : ℂ l2} → sim-ℂ x y → sim-ℂ y x
  symmetric-sim-ℂ (a~c , b~d) = (symmetric-sim-ℝ a~c , symmetric-sim-ℝ b~d)
```

### Similarity is transitive

```agda
abstract
  transitive-sim-ℂ :
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    sim-ℂ y z → sim-ℂ x y → sim-ℂ x z
  transitive-sim-ℂ (a , b) (c , d) (e , f) (c~e , d~f) (a~c , b~d) =
    ( transitive-sim-ℝ a c e c~e a~c , transitive-sim-ℝ b d f d~f b~d)
```

### Similarity characterizes equality at a universe level

```agda
abstract
  eq-sim-ℂ : {l : Level} {x y : ℂ l} → sim-ℂ x y → x ＝ y
  eq-sim-ℂ (a~c , b~d) = eq-ℂ (eq-sim-ℝ a~c) (eq-sim-ℝ b~d)
```

### Similarity is a large equivalence relation

```agda
large-equivalence-relation-sim-ℂ : Large-Equivalence-Relation (_⊔_) ℂ
large-equivalence-relation-sim-ℂ =
  make-Large-Equivalence-Relation
    ( sim-prop-ℂ)
    ( refl-sim-ℂ)
    ( λ _ _ → symmetric-sim-ℂ)
    ( transitive-sim-ℂ)
```

### Similarity is a large similarity relation

```agda
large-similarity-relation-ℂ : Large-Similarity-Relation (_⊔_) ℂ
large-similarity-relation-ℂ =
  make-Large-Similarity-Relation
    ( large-equivalence-relation-sim-ℂ)
    ( λ _ _ → eq-sim-ℂ)
```

### The canonical embedding of real numbers in the complex numbers preserves similarity

```agda
abstract
  preserves-sim-complex-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → sim-ℝ x y →
    sim-ℂ (complex-ℝ x) (complex-ℝ y)
  preserves-sim-complex-ℝ {l1} {l2} x~y =
    ( x~y ,
      transitive-sim-ℝ
        ( raise-ℝ l1 zero-ℝ)
        ( zero-ℝ)
        ( raise-ℝ l2 zero-ℝ)
        ( sim-raise-ℝ l2 zero-ℝ)
        ( symmetric-sim-ℝ (sim-raise-ℝ l1 zero-ℝ)))
```

### Similarity is preserved by negation

```agda
abstract
  preserves-sim-neg-ℂ :
    {l1 l2 : Level} {x : ℂ l1} {y : ℂ l2} →
    sim-ℂ x y → sim-ℂ (neg-ℂ x) (neg-ℂ y)
  preserves-sim-neg-ℂ (a~c , b~d) =
    ( preserves-sim-neg-ℝ a~c , preserves-sim-neg-ℝ b~d)
```

### Similarity reasoning

Similarities between complex numbers can be constructed by similarity reasoning
in the following way:

```text
similarity-reasoning-ℂ
  x ~ℂ y by sim-1
    ~ℂ z by sim-2
```

```agda
infixl 1 similarity-reasoning-ℂ_
infixl 0 step-similarity-reasoning-ℂ

abstract
  similarity-reasoning-ℂ_ :
    {l : Level} → (x : ℂ l) → sim-ℂ x x
  similarity-reasoning-ℂ x = refl-sim-ℂ x

  step-similarity-reasoning-ℂ :
    {l1 l2 : Level} {x : ℂ l1} {y : ℂ l2} →
    sim-ℂ x y → {l3 : Level} → (u : ℂ l3) → sim-ℂ y u → sim-ℂ x u
  step-similarity-reasoning-ℂ {x = x} {y = y} p u q = transitive-sim-ℂ x y u q p

  syntax step-similarity-reasoning-ℂ p u q = p ~ℂ u by q
```
