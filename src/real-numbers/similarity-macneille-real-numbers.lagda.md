# Similarity of MacNeille real numbers

```agda
module real-numbers.similarity-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-equivalence-relations
open import foundation.large-similarity-relations
open import foundation.locally-small-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.similarity-subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.large-preorders

open import real-numbers.macneille-real-numbers
```

</details>

## Idea

Two [MacNeille real numbers](real-numbers.macneille-real-numbers.md) are
{{#concept "similar" Disambiguation="MacNeille real numbers" Agda=sim-macneille-ℝ}}
if they are [less than or equal](real-numbers.inequality-real-numbers.md) to
each other. The similarity relation on real numbers extends the
[equality](foundation-core.identity-types.md) relation to real numbers of
differing universe levels.

## Definition

```agda
module _
  {l1 l2 : Level} (x : macneille-ℝ l1) (y : macneille-ℝ l2)
  where

  opaque
    sim-macneille-ℝ : UU (l1 ⊔ l2)
    sim-macneille-ℝ =
      sim-subtype
        ( lower-cut-macneille-ℝ x)
        ( lower-cut-macneille-ℝ y)

    is-prop-sim-macneille-ℝ : is-prop sim-macneille-ℝ
    is-prop-sim-macneille-ℝ =
      is-prop-type-Prop
        ( sim-prop-subtype
          ( lower-cut-macneille-ℝ x)
          ( lower-cut-macneille-ℝ y))

  sim-prop-macneille-ℝ : Prop (l1 ⊔ l2)
  sim-prop-macneille-ℝ = (sim-macneille-ℝ , is-prop-sim-macneille-ℝ)

  infix 6 _~ℝₘ_
  _~ℝₘ_ : UU (l1 ⊔ l2)
  _~ℝₘ_ = sim-macneille-ℝ
```

## Properties

### Similarity in the MacNeille real numbers is equivalent to similarity of lower cuts

```agda
module _
  {l1 l2 : Level} (x : macneille-ℝ l1) (y : macneille-ℝ l2)
  where

  abstract opaque
    unfolding sim-macneille-ℝ

    sim-lower-cut-iff-sim-macneille-ℝ :
      sim-subtype (lower-cut-macneille-ℝ x) (lower-cut-macneille-ℝ y) ↔
      ( x ~ℝₘ y)
    sim-lower-cut-iff-sim-macneille-ℝ = id-iff
```

### Similarity in the MacNeille real numbers is equivalent to similarity of upper cuts

```agda
module _
  {l1 l2 : Level} (x : macneille-ℝ l1) (y : macneille-ℝ l2)
  where

  abstract opaque
    unfolding sim-macneille-ℝ

    sim-sim-upper-cut-macneille-ℝ :
      sim-subtype (upper-cut-macneille-ℝ x) (upper-cut-macneille-ℝ y) →
      ( x ~ℝₘ y)
    sim-sim-upper-cut-macneille-ℝ =
      sim-lower-cut-sim-upper-cut-macneille-ℝ x y

    sim-upper-cut-sim-macneille-ℝ :
      ( x ~ℝₘ y) →
      sim-subtype (upper-cut-macneille-ℝ x) (upper-cut-macneille-ℝ y)
    sim-upper-cut-sim-macneille-ℝ =
      sim-upper-cut-sim-lower-cut-macneille-ℝ x y

  sim-upper-cut-iff-sim-macneille-ℝ :
    sim-subtype (upper-cut-macneille-ℝ x) (upper-cut-macneille-ℝ y) ↔
    ( x ~ℝₘ y)
  sim-upper-cut-iff-sim-macneille-ℝ =
    ( sim-sim-upper-cut-macneille-ℝ , sim-upper-cut-sim-macneille-ℝ)
```

### Reflexivity

```agda
abstract opaque
  unfolding sim-macneille-ℝ

  refl-sim-macneille-ℝ :
    {l : Level} (x : macneille-ℝ l) → x ~ℝₘ x
  refl-sim-macneille-ℝ x = refl-sim-subtype (lower-cut-macneille-ℝ x)

  sim-eq-macneille-ℝ :
    {l : Level} {x y : macneille-ℝ l} → x ＝ y → x ~ℝₘ y
  sim-eq-macneille-ℝ {_} {x} {y} x=y =
    tr (sim-macneille-ℝ x) x=y (refl-sim-macneille-ℝ x)
```

### Symmetry

```agda
abstract opaque
  unfolding sim-macneille-ℝ

  symmetric-sim-macneille-ℝ :
    {l1 l2 : Level} {x : macneille-ℝ l1} {y : macneille-ℝ l2} →
    x ~ℝₘ y → y ~ℝₘ x
  symmetric-sim-macneille-ℝ {x = x} {y = y} =
    symmetric-sim-subtype
      ( lower-cut-macneille-ℝ x)
      ( lower-cut-macneille-ℝ y)
```

### Transitivity

```agda
abstract opaque
  unfolding sim-macneille-ℝ

  transitive-sim-macneille-ℝ :
    {l1 l2 l3 : Level} →
    (x : macneille-ℝ l1)
    (y : macneille-ℝ l2)
    (z : macneille-ℝ l3) →
    y ~ℝₘ z → x ~ℝₘ y → x ~ℝₘ z
  transitive-sim-macneille-ℝ x y z =
    transitive-sim-subtype
      ( lower-cut-macneille-ℝ x)
      ( lower-cut-macneille-ℝ y)
      ( lower-cut-macneille-ℝ z)
```

### Similar MacNeille real numbers in the same universe are equal

```agda
abstract opaque
  unfolding sim-macneille-ℝ

  eq-sim-macneille-ℝ :
    {l : Level} → {x y : macneille-ℝ l} → x ~ℝₘ y → x ＝ y
  eq-sim-macneille-ℝ {x = x} {y = y} H =
    eq-eq-lower-cut-macneille-ℝ x y (eq-sim-subtype _ _ H)
```

### Similarity is a large similarity relation

```agda
large-preorder-sim-macneille-ℝ :
  Large-Preorder lsuc (_⊔_)
large-preorder-sim-macneille-ℝ =
  make-Large-Preorder macneille-ℝ
    ( sim-prop-macneille-ℝ)
    ( refl-sim-macneille-ℝ)
    ( transitive-sim-macneille-ℝ)

large-equivalence-relation-sim-macneille-ℝ :
  Large-Equivalence-Relation (_⊔_) macneille-ℝ
large-equivalence-relation-sim-macneille-ℝ =
  make-Large-Equivalence-Relation
    ( sim-prop-macneille-ℝ)
    ( refl-sim-macneille-ℝ)
    ( λ _ _ → symmetric-sim-macneille-ℝ)
    ( transitive-sim-macneille-ℝ)

large-similarity-relation-sim-macneille-ℝ :
  Large-Similarity-Relation (_⊔_) macneille-ℝ
large-similarity-relation-sim-macneille-ℝ =
  make-Large-Similarity-Relation
    ( large-equivalence-relation-sim-macneille-ℝ)
    ( λ _ _ → eq-sim-macneille-ℝ)
```

### The MacNeille real numbers at universe `l` are locally small with respect to `UU l`

```agda
abstract
  is-locally-small-macneille-ℝ :
    (l : Level) → is-locally-small l (macneille-ℝ l)
  is-locally-small-macneille-ℝ =
    is-locally-small-type-Large-Similarity-Relation
      ( large-similarity-relation-sim-macneille-ℝ)
```

### Similarity reasoning

Similarities between MacNeille real numbers can be constructed by similarity
reasoning in the following way:

```text
similarity-reasoning-macneille-ℝ
  x ~ℝₘ y by sim-1
    ~ℝₘ z by sim-2
```

```agda
infixl 1 similarity-reasoning-macneille-ℝ_
infixl 0 step-similarity-reasoning-macneille-ℝ

abstract opaque
  unfolding sim-macneille-ℝ

  similarity-reasoning-macneille-ℝ_ :
    {l : Level} (x : macneille-ℝ l) → sim-macneille-ℝ x x
  similarity-reasoning-macneille-ℝ x = refl-sim-macneille-ℝ x

  step-similarity-reasoning-macneille-ℝ :
    {l1 l2 : Level}
    {x : macneille-ℝ l1} {y : macneille-ℝ l2} →
    sim-macneille-ℝ x y →
    {l3 : Level} (u : macneille-ℝ l3) →
    sim-macneille-ℝ y u → sim-macneille-ℝ x u
  step-similarity-reasoning-macneille-ℝ {x = x} {y = y} p u q =
    transitive-sim-macneille-ℝ x y u q p

  syntax step-similarity-reasoning-macneille-ℝ p u q = p ~ℝₘ u by q
```

## See also

- In
  [`real-numbers.equality-real-numbers`](real-numbers.equality-real-numbers.md)
  it is demonstrated that similarity is double negation stable.
