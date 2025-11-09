# Apartness of real numbers

```agda
module real-numbers.apartness-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.binary-transport
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-disjunction
open import foundation.large-apartness-relations
open import foundation.large-binary-relations
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

Two [real numbers](real-numbers.dedekind-real-numbers.md) are
[apart](foundation.large-apartness-relations.md) if one is
[strictly less](real-numbers.strict-inequality-real-numbers.md) than the other.

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  apart-prop-ℝ : Prop (l1 ⊔ l2)
  apart-prop-ℝ = le-prop-ℝ x y ∨ le-prop-ℝ y x

  apart-ℝ : UU (l1 ⊔ l2)
  apart-ℝ = type-Prop apart-prop-ℝ

apart-le-ℝ :
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → le-ℝ x y → apart-ℝ x y
apart-le-ℝ = inl-disjunction
```

## Properties

### Apartness is antireflexive

```agda
antireflexive-apart-ℝ : {l : Level} → (x : ℝ l) → ¬ (apart-ℝ x x)
antireflexive-apart-ℝ x =
  elim-disjunction empty-Prop (irreflexive-le-ℝ x) (irreflexive-le-ℝ x)
```

### Apartness is symmetric

```agda
symmetric-apart-ℝ :
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → apart-ℝ x y → apart-ℝ y x
symmetric-apart-ℝ {x = x} {y = y} =
  elim-disjunction (apart-prop-ℝ y x) inr-disjunction inl-disjunction
```

### Apartness is cotransitive

```agda
cotransitive-apart-ℝ : is-cotransitive-Large-Relation-Prop ℝ apart-prop-ℝ
cotransitive-apart-ℝ x y z =
  elim-disjunction
    ( apart-prop-ℝ x z ∨ apart-prop-ℝ z y)
    ( λ x<y →
      map-disjunction
        ( inl-disjunction)
        ( inl-disjunction)
        ( cotransitive-le-ℝ x y z x<y))
    ( λ y<x →
      elim-disjunction
        ( apart-prop-ℝ x z ∨ apart-prop-ℝ z y)
        ( inr-disjunction ∘ inr-disjunction)
        ( inl-disjunction ∘ inr-disjunction)
        ( cotransitive-le-ℝ y x z y<x))
```

### Apartness on the reals is a large apartness relation

```agda
large-apartness-relation-ℝ : Large-Apartness-Relation _⊔_ ℝ
apart-prop-Large-Apartness-Relation large-apartness-relation-ℝ =
  apart-prop-ℝ
antirefl-Large-Apartness-Relation large-apartness-relation-ℝ =
  antireflexive-apart-ℝ
symmetric-Large-Apartness-Relation large-apartness-relation-ℝ _ _ =
  symmetric-apart-ℝ
cotransitive-Large-Apartness-Relation large-apartness-relation-ℝ =
  cotransitive-apart-ℝ
```

### Apart real numbers are nonequal

```agda
nonequal-apart-ℝ : {l : Level} (x y : ℝ l) → apart-ℝ x y → x ≠ y
nonequal-apart-ℝ x y =
  nonequal-apart-Large-Apartness-Relation large-apartness-relation-ℝ
```

### Apartness is preserved by translation

```agda
abstract
  preserves-apart-left-add-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    apart-ℝ y z → apart-ℝ (x +ℝ y) (x +ℝ z)
  preserves-apart-left-add-ℝ x y z =
    map-disjunction
      ( preserves-le-left-add-ℝ x y z)
      ( preserves-le-left-add-ℝ x z y)

  preserves-apart-right-add-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    apart-ℝ y z → apart-ℝ (y +ℝ x) (z +ℝ x)
  preserves-apart-right-add-ℝ x y z y#z =
    binary-tr
      ( apart-ℝ)
      ( commutative-add-ℝ x y)
      ( commutative-add-ℝ x z)
      ( preserves-apart-left-add-ℝ x y z y#z)
```

### Apartness is preserved by negation

```agda
abstract
  preserves-apart-neg-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → apart-ℝ x y →
    apart-ℝ (neg-ℝ x) (neg-ℝ y)
  preserves-apart-neg-ℝ x y =
    elim-disjunction
      ( apart-prop-ℝ _ _)
      ( inr-disjunction ∘ neg-le-ℝ)
      ( inl-disjunction ∘ neg-le-ℝ)
```

### Apartness is preserved by similarity

```agda
abstract
  apart-right-sim-ℝ :
    {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3) →
    sim-ℝ x y → apart-ℝ z x → apart-ℝ z y
  apart-right-sim-ℝ z x y x~y =
    map-disjunction
      ( preserves-le-right-sim-ℝ z x y x~y)
      ( preserves-le-left-sim-ℝ z x y x~y)

  apart-left-sim-ℝ :
    {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3) →
    sim-ℝ x y → apart-ℝ x z → apart-ℝ y z
  apart-left-sim-ℝ z x y x~y =
    map-disjunction
      ( preserves-le-left-sim-ℝ z x y x~y)
      ( preserves-le-right-sim-ℝ z x y x~y)

  apart-sim-ℝ :
    {l1 l2 l3 l4 : Level} {x : ℝ l1} {x' : ℝ l2} {y : ℝ l3} {y' : ℝ l4} →
    sim-ℝ x x' → sim-ℝ y y' → apart-ℝ x y → apart-ℝ x' y'
  apart-sim-ℝ {x = x} {x' = x'} {y = y} {y' = y'} x~x' y~y' x#y =
    apart-left-sim-ℝ
      ( y')
      ( x)
      ( x')
      ( x~x')
      ( apart-right-sim-ℝ
        ( x)
        ( y)
        ( y')
        ( y~y')
        ( x#y))
```
