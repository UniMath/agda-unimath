# The type of decreasing binary sequences

```agda
module set-theory.decreasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation-stable-equality
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.injective-maps
open import foundation.maybe
open import foundation.negated-equality
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.tight-apartness-relations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.identity-types

open import set-theory.cantor-space
```

</details>

## Idea

The type of
{{#concept "decreasing binary sequences" Agda=decreasing-binary-sequence-ℕ}}is
the [subset](foundation-core.subtypes.md) of the
[cantor set](set-theory.cantor-space.md) consisting of decreasing sequences of
binary numbers. This type is equivalent to the
[conatural numbers](elementary-number-theory.conatural-numbers.md).

We follow formalizations from the TypeTopology library. {{#cite TypeTopology}}

## Definitions

```agda
is-decreasing-binary-sequence-ℕ :
  cantor-space → UU lzero
is-decreasing-binary-sequence-ℕ x =
  (n : ℕ) → is-false (x n) → is-false (x (succ-ℕ n))

is-prop-is-decreasing-binary-sequence-ℕ :
  (x : cantor-space) → is-prop (is-decreasing-binary-sequence-ℕ x)
is-prop-is-decreasing-binary-sequence-ℕ x =
  is-prop-Π (λ n → is-prop-function-type (is-prop-is-false (x (succ-ℕ n))))

is-decreasing-binary-sequence-ℕ-Prop :
  cantor-space → Prop lzero
is-decreasing-binary-sequence-ℕ-Prop x =
  ( is-decreasing-binary-sequence-ℕ x ,
    is-prop-is-decreasing-binary-sequence-ℕ x)
```

### The generic convergent sequence

```agda
decreasing-binary-sequence-ℕ : UU lzero
decreasing-binary-sequence-ℕ = Σ cantor-space is-decreasing-binary-sequence-ℕ

map-cantor-space-decreasing-binary-sequence-ℕ :
  decreasing-binary-sequence-ℕ → cantor-space
map-cantor-space-decreasing-binary-sequence-ℕ = pr1

emb-cantor-space-decreasing-binary-sequence-ℕ :
  decreasing-binary-sequence-ℕ ↪ cantor-space
emb-cantor-space-decreasing-binary-sequence-ℕ =
  emb-subtype is-decreasing-binary-sequence-ℕ-Prop
```

### The element at infinity

```agda
infinity-decreasing-binary-sequence-ℕ : decreasing-binary-sequence-ℕ
infinity-decreasing-binary-sequence-ℕ = (const ℕ true , λ where n ())
```

### The zero element

We interpret the constantly zero sequence as the zero element of the generic
convergent sequence.

```agda
zero-decreasing-binary-sequence-ℕ : decreasing-binary-sequence-ℕ
zero-decreasing-binary-sequence-ℕ = (const ℕ false , λ n x → refl)
```

### The successor function

```agda
succ-decreasing-binary-sequence-ℕ :
  decreasing-binary-sequence-ℕ → decreasing-binary-sequence-ℕ
succ-decreasing-binary-sequence-ℕ (x , H) =
  rec-ℕ true (λ n _ → x n) , ind-ℕ (λ where ()) (λ n _ → H n)
```

### The predecessor function

```agda
decons-decreasing-binary-sequence-ℕ :
  decreasing-binary-sequence-ℕ → Maybe decreasing-binary-sequence-ℕ
decons-decreasing-binary-sequence-ℕ (x , H) =
  rec-bool (unit-Maybe (x ∘ succ-ℕ , H ∘ succ-ℕ)) exception-Maybe (x 0)
```

### The constructor function

```agda
cons-decreasing-binary-sequence-ℕ :
  Maybe decreasing-binary-sequence-ℕ → decreasing-binary-sequence-ℕ
cons-decreasing-binary-sequence-ℕ (inl x) = succ-decreasing-binary-sequence-ℕ x
cons-decreasing-binary-sequence-ℕ (inr x) = zero-decreasing-binary-sequence-ℕ
```

### The canonical inclusion of the natural numbers

```agda
inclusion-decreasing-binary-sequence-ℕ : ℕ → decreasing-binary-sequence-ℕ
inclusion-decreasing-binary-sequence-ℕ =
  rec-ℕ
    ( zero-decreasing-binary-sequence-ℕ)
    ( λ _ → succ-decreasing-binary-sequence-ℕ)
```

### Some other constant

```agda
one-decreasing-binary-sequence-ℕ : decreasing-binary-sequence-ℕ
one-decreasing-binary-sequence-ℕ = inclusion-decreasing-binary-sequence-ℕ 1

two-decreasing-binary-sequence-ℕ : decreasing-binary-sequence-ℕ
two-decreasing-binary-sequence-ℕ = inclusion-decreasing-binary-sequence-ℕ 2

three-decreasing-binary-sequence-ℕ : decreasing-binary-sequence-ℕ
three-decreasing-binary-sequence-ℕ = inclusion-decreasing-binary-sequence-ℕ 3
```

## Properties

### Equality on elements of the generic convergent sequence

```agda
Eq-decreasing-binary-sequence-ℕ :
  decreasing-binary-sequence-ℕ → decreasing-binary-sequence-ℕ → UU lzero
Eq-decreasing-binary-sequence-ℕ x y = pr1 x ~ pr1 y

refl-Eq-decreasing-binary-sequence-ℕ :
  (x : decreasing-binary-sequence-ℕ) → Eq-decreasing-binary-sequence-ℕ x x
refl-Eq-decreasing-binary-sequence-ℕ x = refl-htpy

extensionality-decreasing-binary-sequence-ℕ :
  (x y : decreasing-binary-sequence-ℕ) →
  (x ＝ y) ≃ Eq-decreasing-binary-sequence-ℕ x y
extensionality-decreasing-binary-sequence-ℕ x y =
  equiv-funext ∘e
  equiv-ap-inclusion-subtype is-decreasing-binary-sequence-ℕ-Prop

Eq-eq-decreasing-binary-sequence-ℕ :
  {x y : decreasing-binary-sequence-ℕ} →
  x ＝ y → Eq-decreasing-binary-sequence-ℕ x y
Eq-eq-decreasing-binary-sequence-ℕ {x} {y} =
  map-equiv (extensionality-decreasing-binary-sequence-ℕ x y)

eq-Eq-decreasing-binary-sequence-ℕ :
  {x y : decreasing-binary-sequence-ℕ} →
  Eq-decreasing-binary-sequence-ℕ x y → x ＝ y
eq-Eq-decreasing-binary-sequence-ℕ {x} {y} =
  map-inv-equiv (extensionality-decreasing-binary-sequence-ℕ x y)
```

### The tight apartness relation on decreasing binary sequences

```agda
tight-apartness-relation-decreasing-binary-sequence-ℕ :
  Tight-Apartness-Relation lzero decreasing-binary-sequence-ℕ
tight-apartness-relation-decreasing-binary-sequence-ℕ =
  type-subtype-Tight-Apartness-Relation
    is-decreasing-binary-sequence-ℕ-Prop
    tight-apartness-relation-cantor-space

decreasing-binary-sequence-ℕ-Type-With-Tight-Apartness :
  Type-With-Tight-Apartness lzero lzero
decreasing-binary-sequence-ℕ-Type-With-Tight-Apartness =
  subtype-Type-With-Tight-Apartness
    cantor-space-Type-With-Tight-Apartness
    is-decreasing-binary-sequence-ℕ-Prop
```

### The type of decreasing binary sequences has double negation stable equality

```agda
has-double-negation-stable-equality-decreasing-binary-sequence-ℕ :
  has-double-negation-stable-equality decreasing-binary-sequence-ℕ
has-double-negation-stable-equality-decreasing-binary-sequence-ℕ =
  has-double-negation-stable-equality-type-Type-With-Tight-Apartness
    ( decreasing-binary-sequence-ℕ-Type-With-Tight-Apartness)
```

### The type of decreasing binary sequences is a fixed point of the maybe monad

```agda
is-section-cons-decreasing-binary-sequence-ℕ :
  is-section decons-decreasing-binary-sequence-ℕ cons-decreasing-binary-sequence-ℕ
is-section-cons-decreasing-binary-sequence-ℕ (inl x) = refl
is-section-cons-decreasing-binary-sequence-ℕ (inr x) = refl

-- is-retraction-cons-decreasing-binary-sequence-ℕ : is-retraction decons-decreasing-binary-sequence-ℕ cons-decreasing-binary-sequence-ℕ
-- is-retraction-cons-decreasing-binary-sequence-ℕ (x , H) =
--   eq-Eq-decreasing-binary-sequence-ℕ (ind-ℕ (equational-reasoning {! pr1 ((cons-decreasing-binary-sequence-ℕ ∘ decons-decreasing-binary-sequence-ℕ) (x , H)) 0 !} ＝ {! x 0 !} by {!   !}) {!   !})
```

## External links

- [CoNaturals](https://martinescardo.github.io/TypeTopology/CoNaturals.index.html)
  at TypeTopology
- [extended natural numbers](https://ncatlab.org/nlab/show/extended+natural+number)
  at $n$Lab
