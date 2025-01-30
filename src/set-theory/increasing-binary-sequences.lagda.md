# The type of increasing binary sequences

```agda
module set-theory.increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation-stable-equality
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.inequality-booleans
open import foundation.injective-maps
open import foundation.logical-operations-booleans
open import foundation.maybe
open import foundation.negated-equality
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.tight-apartness-relations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.identity-types

open import order-theory.order-preserving-maps-posets

open import set-theory.cantor-space
```

</details>

## Idea

The type of
{{#concept "increasing binary sequences" Agda=increasing-binary-sequence-ℕ}}is
the [subset](foundation-core.subtypes.md) of the
[cantor set](set-theory.cantor-space.md) consisting of increasing sequences of
binary numbers. This type is equivalent to the
[conatural numbers](elementary-number-theory.conatural-numbers.md).

We follow formalizations from the TypeTopology library. {{#cite TypeTopology}}

## Definitions

### The predicate on a binary sequence of being increasing

```agda
is-increasing-binary-sequence-ℕ :
  cantor-space → UU lzero
is-increasing-binary-sequence-ℕ x =
  (n : ℕ) → leq-bool (x n) (x (succ-ℕ n))

is-prop-is-increasing-binary-sequence-ℕ :
  (x : cantor-space) → is-prop (is-increasing-binary-sequence-ℕ x)
is-prop-is-increasing-binary-sequence-ℕ x =
  is-prop-Π (λ n → is-prop-leq-bool {x n} {x (succ-ℕ n)})

is-increasing-binary-sequence-ℕ-Prop :
  cantor-space → Prop lzero
is-increasing-binary-sequence-ℕ-Prop x =
  ( is-increasing-binary-sequence-ℕ x ,
    is-prop-is-increasing-binary-sequence-ℕ x)
```

### The type of increasing binary sequences

```agda
increasing-binary-sequence-ℕ : UU lzero
increasing-binary-sequence-ℕ = Σ cantor-space is-increasing-binary-sequence-ℕ

map-cantor-space-increasing-binary-sequence-ℕ :
  increasing-binary-sequence-ℕ → cantor-space
map-cantor-space-increasing-binary-sequence-ℕ = pr1

emb-cantor-space-increasing-binary-sequence-ℕ :
  increasing-binary-sequence-ℕ ↪ cantor-space
emb-cantor-space-increasing-binary-sequence-ℕ =
  emb-subtype is-increasing-binary-sequence-ℕ-Prop
```

### The element at infinity

```agda
infinity-increasing-binary-sequence-ℕ : increasing-binary-sequence-ℕ
infinity-increasing-binary-sequence-ℕ = (const ℕ false , λ n → star)
```

### The zero element

We interpret the constantly zero sequence as the zero element of the generic
convergent sequence.

```agda
zero-increasing-binary-sequence-ℕ : increasing-binary-sequence-ℕ
zero-increasing-binary-sequence-ℕ = (const ℕ true , λ n → star)
```

### The successor function

```agda
succ-increasing-binary-sequence-ℕ :
  increasing-binary-sequence-ℕ → increasing-binary-sequence-ℕ
succ-increasing-binary-sequence-ℕ (x , H) =
  (rec-ℕ false (λ n _ → x n) , ind-ℕ (min-leq-bool {x 0}) (λ n _ → H n))
```

### The predecessor function

```agda
decons-increasing-binary-sequence-ℕ :
  increasing-binary-sequence-ℕ → Maybe increasing-binary-sequence-ℕ
decons-increasing-binary-sequence-ℕ (x , H) =
  rec-bool exception-Maybe (unit-Maybe (x ∘ succ-ℕ , H ∘ succ-ℕ)) (x 0)
```

### The constructor function

```agda
cons-increasing-binary-sequence-ℕ :
  Maybe increasing-binary-sequence-ℕ → increasing-binary-sequence-ℕ
cons-increasing-binary-sequence-ℕ (inl x) = succ-increasing-binary-sequence-ℕ x
cons-increasing-binary-sequence-ℕ (inr x) = zero-increasing-binary-sequence-ℕ
```

## Properties

### Equality on elements of the generic convergent sequence

```agda
Eq-increasing-binary-sequence-ℕ :
  increasing-binary-sequence-ℕ → increasing-binary-sequence-ℕ → UU lzero
Eq-increasing-binary-sequence-ℕ x y = pr1 x ~ pr1 y

refl-Eq-increasing-binary-sequence-ℕ :
  (x : increasing-binary-sequence-ℕ) → Eq-increasing-binary-sequence-ℕ x x
refl-Eq-increasing-binary-sequence-ℕ x = refl-htpy

extensionality-increasing-binary-sequence-ℕ :
  (x y : increasing-binary-sequence-ℕ) →
  (x ＝ y) ≃ Eq-increasing-binary-sequence-ℕ x y
extensionality-increasing-binary-sequence-ℕ x y =
  equiv-funext ∘e
  equiv-ap-inclusion-subtype is-increasing-binary-sequence-ℕ-Prop

Eq-eq-increasing-binary-sequence-ℕ :
  {x y : increasing-binary-sequence-ℕ} →
  x ＝ y → Eq-increasing-binary-sequence-ℕ x y
Eq-eq-increasing-binary-sequence-ℕ {x} {y} =
  map-equiv (extensionality-increasing-binary-sequence-ℕ x y)

eq-Eq-increasing-binary-sequence-ℕ :
  {x y : increasing-binary-sequence-ℕ} →
  Eq-increasing-binary-sequence-ℕ x y → x ＝ y
eq-Eq-increasing-binary-sequence-ℕ {x} {y} =
  map-inv-equiv (extensionality-increasing-binary-sequence-ℕ x y)
```

### The tight apartness relation on increasing binary sequences

```agda
tight-apartness-relation-increasing-binary-sequence-ℕ :
  Tight-Apartness-Relation lzero increasing-binary-sequence-ℕ
tight-apartness-relation-increasing-binary-sequence-ℕ =
  type-subtype-Tight-Apartness-Relation
    is-increasing-binary-sequence-ℕ-Prop
    tight-apartness-relation-cantor-space

increasing-binary-sequence-ℕ-Type-With-Tight-Apartness :
  Type-With-Tight-Apartness lzero lzero
increasing-binary-sequence-ℕ-Type-With-Tight-Apartness =
  subtype-Type-With-Tight-Apartness
    cantor-space-Type-With-Tight-Apartness
    is-increasing-binary-sequence-ℕ-Prop
```

### The type of increasing binary sequences has double negation stable equality

```agda
has-double-negation-stable-equality-increasing-binary-sequence-ℕ :
  has-double-negation-stable-equality increasing-binary-sequence-ℕ
has-double-negation-stable-equality-increasing-binary-sequence-ℕ =
  has-double-negation-stable-equality-type-Type-With-Tight-Apartness
    ( increasing-binary-sequence-ℕ-Type-With-Tight-Apartness)
```

### The type of increasing binary sequences is a set

```agda
is-set-increasing-binary-sequence-ℕ : is-set increasing-binary-sequence-ℕ
is-set-increasing-binary-sequence-ℕ =
  is-set-type-Type-With-Tight-Apartness
    ( increasing-binary-sequence-ℕ-Type-With-Tight-Apartness)
```

### The successor function is injective

```agda
is-injective-succ-increasing-binary-sequence-ℕ :
  is-injective succ-increasing-binary-sequence-ℕ
is-injective-succ-increasing-binary-sequence-ℕ p =
  eq-Eq-increasing-binary-sequence-ℕ
    ( Eq-eq-increasing-binary-sequence-ℕ p ∘ succ-ℕ)
```

### Zero is not a successor of any increasing binary sequence

```agda
neq-zero-succ-increasing-binary-sequence-ℕ :
  {x : increasing-binary-sequence-ℕ} →
  zero-increasing-binary-sequence-ℕ ≠ succ-increasing-binary-sequence-ℕ x
neq-zero-succ-increasing-binary-sequence-ℕ p =
  neq-true-false-bool (Eq-eq-increasing-binary-sequence-ℕ p 0)

neq-succ-zero-increasing-binary-sequence-ℕ :
  {x : increasing-binary-sequence-ℕ} →
  succ-increasing-binary-sequence-ℕ x ≠ zero-increasing-binary-sequence-ℕ
neq-succ-zero-increasing-binary-sequence-ℕ p =
  neq-false-true-bool (Eq-eq-increasing-binary-sequence-ℕ p 0)
```

### The type of increasing binary sequences is a fixed point of the maybe monad

```agda
is-section-cons-increasing-binary-sequence-ℕ :
  is-section
    ( decons-increasing-binary-sequence-ℕ)
    ( cons-increasing-binary-sequence-ℕ)
is-section-cons-increasing-binary-sequence-ℕ (inl x) = refl
is-section-cons-increasing-binary-sequence-ℕ (inr x) = refl

is-injective-cons-increasing-binary-sequence-ℕ :
  is-injective cons-increasing-binary-sequence-ℕ
is-injective-cons-increasing-binary-sequence-ℕ =
  is-injective-has-retraction
    cons-increasing-binary-sequence-ℕ
    decons-increasing-binary-sequence-ℕ
    is-section-cons-increasing-binary-sequence-ℕ

-- is-injective-decons-increasing-binary-sequence-ℕ :
--   is-injective decons-increasing-binary-sequence-ℕ
-- is-injective-decons-increasing-binary-sequence-ℕ {x , H} {y , K} p =
--   eq-Eq-increasing-binary-sequence-ℕ (ind-ℕ {!   !} {!   !})
```

### The type of increasing binary sequences as a retract of the cantor space

```agda
force-increasing-binary-sequence-ℕ' : cantor-space → cantor-space
force-increasing-binary-sequence-ℕ' x zero-ℕ = x zero-ℕ
force-increasing-binary-sequence-ℕ' x (succ-ℕ n) =
  or-bool (x (succ-ℕ n)) (force-increasing-binary-sequence-ℕ' x n)

is-increasing-force-increasing-binary-sequence-ℕ :
  (x : cantor-space) →
  is-increasing-binary-sequence-ℕ (force-increasing-binary-sequence-ℕ' x)
is-increasing-force-increasing-binary-sequence-ℕ x n =
  leq-or-bool' {x (succ-ℕ n)} {force-increasing-binary-sequence-ℕ' x n}

force-increasing-binary-sequence-ℕ : cantor-space → increasing-binary-sequence-ℕ
force-increasing-binary-sequence-ℕ x =
  ( force-increasing-binary-sequence-ℕ' x ,
    is-increasing-force-increasing-binary-sequence-ℕ x)

abstract
  compute-force-increasing-binary-sequence-ℕ' :
    (x : cantor-space) → is-increasing-binary-sequence-ℕ x →
    force-increasing-binary-sequence-ℕ' x ~ x
  compute-force-increasing-binary-sequence-ℕ' x H zero-ℕ = refl
  compute-force-increasing-binary-sequence-ℕ' x H (succ-ℕ n) =
    ( ap
      ( or-bool (x (succ-ℕ n)))
      ( compute-force-increasing-binary-sequence-ℕ' x H n)) ∙
    ( antisymmetric-leq-bool
      ( leq-right-or-bool {x n} {x (succ-ℕ n)} (H n))
      ( leq-or-bool {x (succ-ℕ n)} {x n}))

is-retraction-force-increasing-binary-sequence-ℕ :
  is-retraction
    map-cantor-space-increasing-binary-sequence-ℕ
    force-increasing-binary-sequence-ℕ
is-retraction-force-increasing-binary-sequence-ℕ (x , H) =
  eq-Eq-increasing-binary-sequence-ℕ
    ( compute-force-increasing-binary-sequence-ℕ' x H)

retraction-map-cantor-space-increasing-binary-sequence-ℕ :
  retraction map-cantor-space-increasing-binary-sequence-ℕ
retraction-map-cantor-space-increasing-binary-sequence-ℕ =
  ( force-increasing-binary-sequence-ℕ ,
    is-retraction-force-increasing-binary-sequence-ℕ)

retract-cantor-space-increasing-binary-sequence-ℕ :
  increasing-binary-sequence-ℕ retract-of cantor-space
retract-cantor-space-increasing-binary-sequence-ℕ =
  ( map-cantor-space-increasing-binary-sequence-ℕ ,
    retraction-map-cantor-space-increasing-binary-sequence-ℕ)
```

### Increasing binary sequences are order preserving maps

```agda
preserves-order-increasing-binary-sequence-ℕ :
  {x : increasing-binary-sequence-ℕ} →
  preserves-order-Poset ℕ-Poset bool-Poset (pr1 x)
preserves-order-increasing-binary-sequence-ℕ {x} =
  preserves-order-ind-ℕ-Poset bool-Poset (pr1 x) (pr2 x)

is-increasing-preserves-order-binary-sequence-ℕ :
  {x : cantor-space} →
  preserves-order-Poset ℕ-Poset bool-Poset x →
  is-increasing-binary-sequence-ℕ x
is-increasing-preserves-order-binary-sequence-ℕ H n =
  H n (succ-ℕ n) (succ-leq-ℕ n)
```

## See also

- [The conatural numbers](elementary-number-theory.conatural-numbers.md)

## External links

- [CoNaturals](https://martinescardo.github.io/TypeTopology/CoNaturals.index.html)
  at TypeTopology
- [extended natural numbers](https://ncatlab.org/nlab/show/extended+natural+number)
  at $n$Lab
