# Similarity of real numbers

```agda
module real-numbers.similarity-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.complements-subtypes
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-equivalence-relations
open import foundation.large-similarity-relations
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.similarity-of-elements-large-posets

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

Two [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) are
{{#concept "similar" Disambiguation="Dedekind real numbers" Agda=sim-ℝ}} if they
are [less than or equal](real-numbers.inequality-real-numbers.md) to each other.
The similarity relation on real numbers extends the
[equality](foundation-core.identity-types.md) relation to real numbers of
differing universe levels.

## Definition

```agda
opaque
  sim-ℝ : {l1 l2 : Level} → ℝ l1 → ℝ l2 → UU (l1 ⊔ l2)
  sim-ℝ x y = sim-subtype (lower-cut-ℝ x) (lower-cut-ℝ y)

  is-prop-sim-ℝ : {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → is-prop (sim-ℝ x y)
  is-prop-sim-ℝ x y =
    is-prop-type-Prop (sim-prop-subtype (lower-cut-ℝ x) (lower-cut-ℝ y))

sim-prop-ℝ : {l1 l2 : Level} → ℝ l1 → ℝ l2 → Prop (l1 ⊔ l2)
sim-prop-ℝ x y = (sim-ℝ x y , is-prop-sim-ℝ x y)

infix 6 _~ℝ_
_~ℝ_ : {l1 l2 : Level} → ℝ l1 → ℝ l2 → UU (l1 ⊔ l2)
_~ℝ_ = sim-ℝ
```

## Properties

### Similarity in the real numbers is equivalent to similarity of lower cuts

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    unfolding sim-ℝ

    sim-lower-cut-iff-sim-ℝ :
      sim-subtype (lower-cut-ℝ x) (lower-cut-ℝ y) ↔ (x ~ℝ y)
    sim-lower-cut-iff-sim-ℝ = id-iff
```

### Similarity in the real numbers is equivalent to similarity of upper cuts

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    unfolding sim-ℝ

    sim-sim-upper-cut-ℝ : sim-subtype (upper-cut-ℝ x) (upper-cut-ℝ y) → (x ~ℝ y)
    sim-sim-upper-cut-ℝ = sim-lower-cut-sim-upper-cut-ℝ x y

    sim-upper-cut-sim-ℝ : (x ~ℝ y) → sim-subtype (upper-cut-ℝ x) (upper-cut-ℝ y)
    sim-upper-cut-sim-ℝ = sim-upper-cut-sim-lower-cut-ℝ x y

  sim-upper-cut-iff-sim-ℝ :
    sim-subtype (upper-cut-ℝ x) (upper-cut-ℝ y) ↔ (x ~ℝ y)
  sim-upper-cut-iff-sim-ℝ = (sim-sim-upper-cut-ℝ , sim-upper-cut-sim-ℝ)
```

### Reflexivity

```agda
opaque
  unfolding sim-ℝ

  refl-sim-ℝ : {l : Level} → (x : ℝ l) → x ~ℝ x
  refl-sim-ℝ x = refl-sim-subtype (lower-cut-ℝ x)

  sim-eq-ℝ : {l : Level} → {x y : ℝ l} → x ＝ y → x ~ℝ y
  sim-eq-ℝ {_} {x} {y} x=y = tr (sim-ℝ x) x=y (refl-sim-ℝ x)
```

### Symmetry

```agda
opaque
  unfolding sim-ℝ

  symmetric-sim-ℝ :
    {l1 l2 : Level} → {x : ℝ l1} {y : ℝ l2} → x ~ℝ y → y ~ℝ x
  symmetric-sim-ℝ {x = x} {y = y} =
    symmetric-sim-subtype (lower-cut-ℝ x) (lower-cut-ℝ y)
```

### Transitivity

```agda
opaque
  unfolding sim-ℝ

  transitive-sim-ℝ :
    {l1 l2 l3 : Level} →
    (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    y ~ℝ z → x ~ℝ y → x ~ℝ z
  transitive-sim-ℝ x y z =
    transitive-sim-subtype (lower-cut-ℝ x) (lower-cut-ℝ y) (lower-cut-ℝ z)
```

### Similar real numbers in the same universe are equal

```agda
opaque
  unfolding sim-ℝ

  eq-sim-ℝ : {l : Level} → {x y : ℝ l} → x ~ℝ y → x ＝ y
  eq-sim-ℝ {x = x} {y = y} H = eq-eq-lower-cut-ℝ x y (eq-sim-subtype _ _ H)
```

### Similarity is a large similarity relation

```agda
large-preorder-sim-ℝ : Large-Preorder lsuc _⊔_
large-preorder-sim-ℝ =
  make-Large-Preorder ℝ sim-prop-ℝ refl-sim-ℝ transitive-sim-ℝ

large-equivalence-relation-sim-ℝ : Large-Equivalence-Relation lsuc _⊔_
large-equivalence-relation-sim-ℝ =
  make-Large-Equivalence-Relation large-preorder-sim-ℝ (λ x y → symmetric-sim-ℝ)

large-similarity-relation-sim-ℝ : Large-Similarity-Relation lsuc _⊔_
large-similarity-relation-sim-ℝ =
  make-Large-Similarity-Relation
    ( large-equivalence-relation-sim-ℝ)
    ( λ _ _ → eq-sim-ℝ)
```

### Similarity reasoning

Similarities between real numbers can be constructed by similarity reasoning in
the following way:

```text
similarity-reasoning-ℝ
  x ~ℝ y by sim-1
    ~ℝ z by sim-2
```

```agda
infixl 1 similarity-reasoning-ℝ_
infixl 0 step-similarity-reasoning-ℝ

opaque
  unfolding sim-ℝ

  similarity-reasoning-ℝ_ :
    {l : Level} → (x : ℝ l) → sim-ℝ x x
  similarity-reasoning-ℝ x = refl-sim-ℝ x

  step-similarity-reasoning-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
    sim-ℝ x y → {l3 : Level} → (u : ℝ l3) → sim-ℝ y u → sim-ℝ x u
  step-similarity-reasoning-ℝ {x = x} {y = y} p u q = transitive-sim-ℝ x y u q p

  syntax step-similarity-reasoning-ℝ p u q = p ~ℝ u by q
```
