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

open import order-theory.increasing-sequences-posets
open import order-theory.order-preserving-maps-posets

open import set-theory.cantor-space
```

</details>

## Idea

The type of
{{#concept "increasing binary sequences" WD="Extended natural numbers" WDID=Q105759800 Agda=ℕ∞↗}}
`ℕ∞↗` is the [subset](foundation-core.subtypes.md) of the
[cantor set](set-theory.cantor-space.md) consisting of increasing sequences of
binary numbers. This type is equivalent to the
[conatural numbers](elementary-number-theory.conatural-numbers.md) `ℕ∞`.

Many of these formalizations mirror work from the TypeTopology library.
{{#cite TypeTopology}}

## Definitions

### The predicate on a binary sequence of being increasing

```agda
is-increasing-binary-sequence : cantor-space → UU lzero
is-increasing-binary-sequence x = (n : ℕ) → leq-bool (x n) (x (succ-ℕ n))

is-prop-is-increasing-binary-sequence :
  (x : cantor-space) → is-prop (is-increasing-binary-sequence x)
is-prop-is-increasing-binary-sequence x =
  is-prop-Π (λ n → is-prop-leq-bool {x n} {x (succ-ℕ n)})

is-increasing-binary-sequence-Prop : cantor-space → Prop lzero
is-increasing-binary-sequence-Prop x =
  ( is-increasing-binary-sequence x ,
    is-prop-is-increasing-binary-sequence x)
```

### The type of increasing binary sequences

```agda
ℕ∞↗ : UU lzero
ℕ∞↗ = Σ cantor-space is-increasing-binary-sequence

sequence-ℕ∞↗ : ℕ∞↗ → cantor-space
sequence-ℕ∞↗ = pr1

is-increasing-sequence-ℕ∞↗ :
  (x : ℕ∞↗) → is-increasing-binary-sequence (sequence-ℕ∞↗ x)
is-increasing-sequence-ℕ∞↗ = pr2

emb-sequence-ℕ∞↗ : ℕ∞↗ ↪ cantor-space
emb-sequence-ℕ∞↗ = emb-subtype is-increasing-binary-sequence-Prop

is-injective-sequence-ℕ∞↗ : is-injective sequence-ℕ∞↗
is-injective-sequence-ℕ∞↗ = is-injective-emb emb-sequence-ℕ∞↗
```

### The element at infinity

```agda
infinity-ℕ∞↗ : ℕ∞↗
infinity-ℕ∞↗ = (const ℕ false , λ _ → star)
```

### The zero element

We interpret the constantly zero sequence as the zero element of the generic
convergent sequence.

```agda
zero-ℕ∞↗ : ℕ∞↗
zero-ℕ∞↗ = (const ℕ true , λ _ → star)
```

### The successor function

```agda
succ-ℕ∞↗ : ℕ∞↗ → ℕ∞↗
succ-ℕ∞↗ (x , H) =
  ( rec-ℕ false (λ n _ → x n) , ind-ℕ (leq-false-bool {x 0}) (λ n _ → H n))
```

### The predecessor function

```agda
shift-left-ℕ∞↗ : ℕ∞↗ → ℕ∞↗
shift-left-ℕ∞↗ (x , H) = (x ∘ succ-ℕ , H ∘ succ-ℕ)

decons-ℕ∞↗ : ℕ∞↗ → Maybe ℕ∞↗
decons-ℕ∞↗ (x , H) =
  rec-bool exception-Maybe (unit-Maybe (shift-left-ℕ∞↗ (x , H))) (x 0)
```

### The constructor function

```agda
cons-ℕ∞↗ : Maybe ℕ∞↗ → ℕ∞↗
cons-ℕ∞↗ (inl x) = succ-ℕ∞↗ x
cons-ℕ∞↗ (inr x) = zero-ℕ∞↗
```

### Some other constants

```agda
one-ℕ∞↗ : ℕ∞↗
one-ℕ∞↗ = succ-ℕ∞↗ zero-ℕ∞↗

two-ℕ∞↗ : ℕ∞↗
two-ℕ∞↗ = succ-ℕ∞↗ one-ℕ∞↗

three-ℕ∞↗ : ℕ∞↗
three-ℕ∞↗ = succ-ℕ∞↗ two-ℕ∞↗
```

## Properties

### Equality on elements of increasing binary sequences

```agda
Eq-ℕ∞↗ : ℕ∞↗ → ℕ∞↗ → UU lzero
Eq-ℕ∞↗ x y = pr1 x ~ pr1 y

refl-Eq-ℕ∞↗ : (x : ℕ∞↗) → Eq-ℕ∞↗ x x
refl-Eq-ℕ∞↗ x = refl-htpy

extensionality-ℕ∞↗ : (x y : ℕ∞↗) → (x ＝ y) ≃ Eq-ℕ∞↗ x y
extensionality-ℕ∞↗ x y =
  equiv-funext ∘e equiv-ap-inclusion-subtype is-increasing-binary-sequence-Prop

Eq-eq-ℕ∞↗ : {x y : ℕ∞↗} → x ＝ y → Eq-ℕ∞↗ x y
Eq-eq-ℕ∞↗ {x} {y} = map-equiv (extensionality-ℕ∞↗ x y)

eq-Eq-ℕ∞↗ : {x y : ℕ∞↗} → Eq-ℕ∞↗ x y → x ＝ y
eq-Eq-ℕ∞↗ {x} {y} = map-inv-equiv (extensionality-ℕ∞↗ x y)
```

### The tight apartness relation on increasing binary sequences

```agda
tight-apartness-relation-ℕ∞↗ : Tight-Apartness-Relation lzero ℕ∞↗
tight-apartness-relation-ℕ∞↗ =
  type-subtype-Tight-Apartness-Relation
    is-increasing-binary-sequence-Prop
    tight-apartness-relation-cantor-space

ℕ∞↗-Type-With-Tight-Apartness : Type-With-Tight-Apartness lzero lzero
ℕ∞↗-Type-With-Tight-Apartness =
  subtype-Type-With-Tight-Apartness
    cantor-space-Type-With-Tight-Apartness
    is-increasing-binary-sequence-Prop
```

### The type of increasing binary sequences has double negation stable equality

```agda
has-double-negation-stable-equality-ℕ∞↗ :
  has-double-negation-stable-equality ℕ∞↗
has-double-negation-stable-equality-ℕ∞↗ =
  has-double-negation-stable-equality-type-Type-With-Tight-Apartness
    ( ℕ∞↗-Type-With-Tight-Apartness)
```

### The type of increasing binary sequences is a set

```agda
abstract
  is-set-ℕ∞↗ : is-set ℕ∞↗
  is-set-ℕ∞↗ =
    is-set-type-Type-With-Tight-Apartness ℕ∞↗-Type-With-Tight-Apartness
```

### The successor function is an embedding

```agda
is-injective-succ-ℕ∞↗ : is-injective succ-ℕ∞↗
is-injective-succ-ℕ∞↗ p = eq-Eq-ℕ∞↗ (Eq-eq-ℕ∞↗ p ∘ succ-ℕ)

abstract
  is-emb-succ-ℕ∞↗ : is-emb succ-ℕ∞↗
  is-emb-succ-ℕ∞↗ = is-emb-is-injective is-set-ℕ∞↗ is-injective-succ-ℕ∞↗

emb-succ-ℕ∞↗ : ℕ∞↗ ↪ ℕ∞↗
emb-succ-ℕ∞↗ = (succ-ℕ∞↗ , is-emb-succ-ℕ∞↗)
```

### Zero is not a successor of any increasing binary sequence

```agda
abstract
  neq-zero-succ-ℕ∞↗ : {x : ℕ∞↗} → zero-ℕ∞↗ ≠ succ-ℕ∞↗ x
  neq-zero-succ-ℕ∞↗ p = neq-true-false-bool (Eq-eq-ℕ∞↗ p 0)

abstract
  neq-succ-zero-ℕ∞↗ : {x : ℕ∞↗} → succ-ℕ∞↗ x ≠ zero-ℕ∞↗
  neq-succ-zero-ℕ∞↗ p = neq-false-true-bool (Eq-eq-ℕ∞↗ p 0)
```

### The constructor is a section of the deconstructor function

```agda
is-section-cons-ℕ∞↗ : is-section decons-ℕ∞↗ cons-ℕ∞↗
is-section-cons-ℕ∞↗ (inl x) = refl
is-section-cons-ℕ∞↗ (inr x) = refl

is-injective-cons-ℕ∞↗ : is-injective cons-ℕ∞↗
is-injective-cons-ℕ∞↗ =
  is-injective-has-retraction cons-ℕ∞↗ decons-ℕ∞↗ is-section-cons-ℕ∞↗
```

### The type of increasing binary sequences as a retract of the cantor space

We can "force" any binary sequence into an increasing binary sequence by
replacing the 𝑛'th value by the least upper bound of all values up to and
including 𝑛. This defines a retract.

```agda
force-ℕ∞↗' : cantor-space → cantor-space
force-ℕ∞↗' x zero-ℕ = x zero-ℕ
force-ℕ∞↗' x (succ-ℕ n) = or-bool (x (succ-ℕ n)) (force-ℕ∞↗' x n)

abstract
  is-increasing-force-ℕ∞↗ :
    (x : cantor-space) → is-increasing-binary-sequence (force-ℕ∞↗' x)
  is-increasing-force-ℕ∞↗ x n =
    right-leq-or-bool {x (succ-ℕ n)} {force-ℕ∞↗' x n}

force-ℕ∞↗ : cantor-space → ℕ∞↗
force-ℕ∞↗ x = (force-ℕ∞↗' x , is-increasing-force-ℕ∞↗ x)

abstract
  compute-force-ℕ∞↗' :
    (x : cantor-space) → is-increasing-binary-sequence x → force-ℕ∞↗' x ~ x
  compute-force-ℕ∞↗' x H zero-ℕ = refl
  compute-force-ℕ∞↗' x H (succ-ℕ n) =
    ( ap
      ( or-bool (x (succ-ℕ n)))
      ( compute-force-ℕ∞↗' x H n)) ∙
    ( antisymmetric-leq-bool
      ( leq-right-or-bool {x n} {x (succ-ℕ n)} (H n))
      ( left-leq-or-bool {x (succ-ℕ n)} {x n}))

abstract
  is-retraction-force-ℕ∞↗ : is-retraction sequence-ℕ∞↗ force-ℕ∞↗
  is-retraction-force-ℕ∞↗ (x , H) = eq-Eq-ℕ∞↗ (compute-force-ℕ∞↗' x H)

retraction-sequence-ℕ∞↗ : retraction sequence-ℕ∞↗
retraction-sequence-ℕ∞↗ = (force-ℕ∞↗ , is-retraction-force-ℕ∞↗)

retract-cantor-space-ℕ∞↗ : ℕ∞↗ retract-of cantor-space
retract-cantor-space-ℕ∞↗ = (sequence-ℕ∞↗ , retraction-sequence-ℕ∞↗)

abstract
  Eq-infinity-force-ℕ∞↗-all-false :
    (f : ℕ → bool) →
    ((n : ℕ) → is-false (f n)) →
    Eq-ℕ∞↗ (force-ℕ∞↗ f) infinity-ℕ∞↗
  Eq-infinity-force-ℕ∞↗-all-false f p 0 =
    p 0
  Eq-infinity-force-ℕ∞↗-all-false f p (succ-ℕ n) =
    ( ap (or-bool (f (succ-ℕ n))) (Eq-infinity-force-ℕ∞↗-all-false f p n)) ∙
    ( ap (λ z → or-bool z false) (p (succ-ℕ n))) ∙
    ( right-unit-law-or-bool)

  all-false-eq-infinity-force-ℕ∞↗ :
    (f : ℕ → bool) →
    force-ℕ∞↗ f ＝ infinity-ℕ∞↗ →
    (n : ℕ) → is-false (f n)
  all-false-eq-infinity-force-ℕ∞↗ f p 0 =
    Eq-eq-ℕ∞↗ p 0
  all-false-eq-infinity-force-ℕ∞↗ f p (succ-ℕ n) =
    is-false-is-false-leq-bool
      ( left-leq-or-bool {f (succ-ℕ n)} {sequence-ℕ∞↗ (force-ℕ∞↗ f) n})
      ( Eq-eq-ℕ∞↗ p (succ-ℕ n))
```

### Increasing binary sequences are order preserving maps

```agda
abstract
  preserves-order-ℕ∞↗ :
    {x : ℕ∞↗} → preserves-order-Poset ℕ-Poset bool-Poset (sequence-ℕ∞↗ x)
  preserves-order-ℕ∞↗ {x} =
    preserves-order-ind-ℕ-Poset bool-Poset
      ( sequence-ℕ∞↗ x)
      ( is-increasing-sequence-ℕ∞↗ x)

abstract
  is-increasing-preserves-order-binary-sequence :
    {x : cantor-space} →
    preserves-order-Poset ℕ-Poset bool-Poset x →
    is-increasing-binary-sequence x
  is-increasing-preserves-order-binary-sequence H n =
    H n (succ-ℕ n) (succ-leq-ℕ n)
```

### If an increasing binary sequence is true at the first position, then it is the zero element

```agda
abstract
  Eq-zero-is-zero-ℕ∞↗ :
    (x : ℕ∞↗) → is-true (sequence-ℕ∞↗ x 0) → sequence-ℕ∞↗ x ~ const ℕ true
  Eq-zero-is-zero-ℕ∞↗ x p zero-ℕ = p
  Eq-zero-is-zero-ℕ∞↗ x p (succ-ℕ n) =
    eq-leq-true-bool
      ( transitive-leq-bool
        { true}
        { sequence-ℕ∞↗ x n}
        { sequence-ℕ∞↗ x (succ-ℕ n)}
        ( is-increasing-sequence-ℕ∞↗ x n)
        ( leq-eq-bool (inv (Eq-zero-is-zero-ℕ∞↗ x p n))))

abstract
  eq-zero-is-zero-ℕ∞↗ : (x : ℕ∞↗) → is-true (sequence-ℕ∞↗ x 0) → x ＝ zero-ℕ∞↗
  eq-zero-is-zero-ℕ∞↗ x p = eq-Eq-ℕ∞↗ (Eq-zero-is-zero-ℕ∞↗ x p)
```

### Computing with the left shift operation

```agda
abstract
  Eq-succ-shift-left-ℕ∞↗ :
    (x : ℕ∞↗) →
    is-false (sequence-ℕ∞↗ x 0) →
    Eq-ℕ∞↗ x (succ-ℕ∞↗ (shift-left-ℕ∞↗ x))
  Eq-succ-shift-left-ℕ∞↗ x p zero-ℕ = p
  Eq-succ-shift-left-ℕ∞↗ x p (succ-ℕ n) = refl

  eq-succ-shift-left-ℕ∞↗ :
    (x : ℕ∞↗) →
    is-false (sequence-ℕ∞↗ x 0) →
    x ＝ succ-ℕ∞↗ (shift-left-ℕ∞↗ x)
  eq-succ-shift-left-ℕ∞↗ x p = eq-Eq-ℕ∞↗ (Eq-succ-shift-left-ℕ∞↗ x p)
```

## See also

- [The conatural numbers](elementary-number-theory.conatural-numbers.md)
- [Initial segments of the natural numbers](elementary-number-theory.initial-segments-natural-numbers.md)

## References

{{#bibliography}}

## External links

- [CoNaturals](https://martinescardo.github.io/TypeTopology/CoNaturals.index.html)
  at TypeTopology
- [extended natural numbers](https://ncatlab.org/nlab/show/extended+natural+number)
  at $n$Lab
