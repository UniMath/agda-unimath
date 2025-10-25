# The canonical inclusion of natural numbers into increasing binary sequences

```agda
module set-theory.inclusion-natural-numbers-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
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
open import foundation.equality-coproduct-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.injective-maps
open import foundation.maybe
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universal-property-maybe
open import foundation.universe-levels

open import foundation-core.identity-types

open import logic.double-negation-dense-maps

open import order-theory.order-preserving-maps-posets

open import set-theory.finite-elements-increasing-binary-sequences
open import set-theory.increasing-binary-sequences
open import set-theory.inequality-increasing-binary-sequences
open import set-theory.positive-elements-increasing-binary-sequences
open import set-theory.strict-lower-bounds-increasing-binary-sequences
```

</details>

## Idea

The canonical map `ℕ → ℕ∞↑` defined by induction to send zero to zero, and the
successor of `n` to the successor of the map evaluated at `n` is the
{{#concept "canonical inclusion" Disambiguation="of the natural numbers into increasing binary sequences" Agda=increasing-binseq-ℕ}}.
This map is a [embedding](foundation-core.embeddings.md) of
[sets](foundation-core.sets.md) that is
non-[surjective](foundation.surjective-maps.md), as it does not hit the element
at infinity. We may extend this inclusion by adding a point at infinity

```text
  ℕ + {∞} ↪ ℕ∞↑
```

to obtain a [double negation dense](logic.double-negation-dense-maps.md)
embedding of sets. This map is surjective if and only if the
[weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
holds.

## Definitions

### The canonical inclusion of natural numbers

```agda
increasing-binseq-ℕ : ℕ → ℕ∞↑
increasing-binseq-ℕ = rec-ℕ zero-ℕ∞↑ (λ _ → succ-ℕ∞↑)
```

### The canonical extended inclusion

```agda
increasing-binseq-Maybe-ℕ : Maybe ℕ → ℕ∞↑
increasing-binseq-Maybe-ℕ =
  rec-coproduct increasing-binseq-ℕ (point infinity-ℕ∞↑)
```

## Properties

### The canonical inclusion is an embedding

```agda
abstract
  is-injective-increasing-binseq-ℕ : is-injective increasing-binseq-ℕ
  is-injective-increasing-binseq-ℕ {zero-ℕ} {zero-ℕ} p =
    refl
  is-injective-increasing-binseq-ℕ {zero-ℕ} {succ-ℕ y} p =
    ex-falso (neq-zero-succ-ℕ∞↑ p)
  is-injective-increasing-binseq-ℕ {succ-ℕ x} {zero-ℕ} p =
    ex-falso (neq-succ-zero-ℕ∞↑ p)
  is-injective-increasing-binseq-ℕ {succ-ℕ x} {succ-ℕ y} p =
    ap succ-ℕ (is-injective-increasing-binseq-ℕ (is-injective-succ-ℕ∞↑ p))

abstract
  is-emb-increasing-binseq-ℕ : is-emb increasing-binseq-ℕ
  is-emb-increasing-binseq-ℕ =
    is-emb-is-injective is-set-ℕ∞↑ is-injective-increasing-binseq-ℕ

emb-ℕ∞↑-ℕ : ℕ ↪ ℕ∞↑
emb-ℕ∞↑-ℕ = (increasing-binseq-ℕ , is-emb-increasing-binseq-ℕ)
```

### The canonical inclusion preserves order

```agda
abstract
  preserves-order-increasing-binseq-ℕ :
    preserves-order-Poset ℕ-Poset ℕ∞↑-Poset increasing-binseq-ℕ
  preserves-order-increasing-binseq-ℕ zero-ℕ y p =
    leq-zero-ℕ∞↑ (increasing-binseq-ℕ y)
  preserves-order-increasing-binseq-ℕ
    ( succ-ℕ x) (succ-ℕ y) p =
    preserves-order-succ-ℕ∞↑
      ( increasing-binseq-ℕ x)
      ( increasing-binseq-ℕ y)
      ( preserves-order-increasing-binseq-ℕ x y p)
```

### The canonical inclusion is not surjective

```agda
abstract
  Neq-infinity-increasing-binseq-ℕ :
    (n : ℕ) → ¬ (sequence-ℕ∞↑ (increasing-binseq-ℕ n) ~ const ℕ false)
  Neq-infinity-increasing-binseq-ℕ zero-ℕ H = neq-true-false-bool (H 0)
  Neq-infinity-increasing-binseq-ℕ (succ-ℕ n) H =
    Neq-infinity-increasing-binseq-ℕ n (H ∘ succ-ℕ)

  neq-infinity-increasing-binseq-ℕ :
      (n : ℕ) → increasing-binseq-ℕ n ≠ infinity-ℕ∞↑
  neq-infinity-increasing-binseq-ℕ n =
    map-neg Eq-eq-ℕ∞↑ (Neq-infinity-increasing-binseq-ℕ n)

  is-not-double-negation-dense-increasing-binseq-ℕ :
    ¬ (is-double-negation-dense-map increasing-binseq-ℕ)
  is-not-double-negation-dense-increasing-binseq-ℕ H =
    H infinity-ℕ∞↑ (λ p → neq-infinity-increasing-binseq-ℕ (pr1 p) (pr2 p))

  is-not-surjective-increasing-binseq-ℕ :
    ¬ (is-surjective increasing-binseq-ℕ)
  is-not-surjective-increasing-binseq-ℕ =
    map-neg
      ( is-double-negation-dense-map-is-surjective)
      ( is-not-double-negation-dense-increasing-binseq-ℕ)
```

### The canonical extended inclusion is an embedding

```agda
abstract
  is-emb-increasing-binseq-Maybe-ℕ :
    is-emb increasing-binseq-Maybe-ℕ
  is-emb-increasing-binseq-Maybe-ℕ =
    is-emb-coproduct
      ( is-emb-increasing-binseq-ℕ)
      ( is-emb-is-injective is-set-ℕ∞↑
        ( is-injective-point infinity-ℕ∞↑))
      ( λ n * → neq-infinity-increasing-binseq-ℕ n)

emb-increasing-binseq-Maybe-ℕ : Maybe ℕ ↪ ℕ∞↑
emb-increasing-binseq-Maybe-ℕ =
  ( increasing-binseq-Maybe-ℕ ,
    is-emb-increasing-binseq-Maybe-ℕ)
```

### Natural numbers are finite increasing binary sequences

```agda
upper-bound-increasing-binseq-ℕ :
  (n : ℕ) → upper-bound-ℕ∞↑ (increasing-binseq-ℕ n)
upper-bound-increasing-binseq-ℕ zero-ℕ =
  ( 0 , refl)
upper-bound-increasing-binseq-ℕ (succ-ℕ n) =
  ( succ-ℕ (pr1 (upper-bound-increasing-binseq-ℕ n)) ,
    pr2 (upper-bound-increasing-binseq-ℕ n))

abstract
  is-finite-increasing-binseq-ℕ :
    (n : ℕ) → is-finite-ℕ∞↑ (increasing-binseq-ℕ n)
  is-finite-increasing-binseq-ℕ n =
    unit-trunc-Prop (upper-bound-increasing-binseq-ℕ n)
```

#### Successor condition on the image of the natural numbers

If an increasing binary sequence `x` switches from `false` to `true` at `n + 1`,
then it is the image of `n + 1`.

```agda
abstract
  Eq-succ-criterion-ℕ∞↑ :
    {x : ℕ∞↑} {n : ℕ} →
    is-strictly-bounded-below-ℕ∞↑ n x →
    is-bounded-ℕ∞↑ x (succ-ℕ n) →
    Eq-ℕ∞↑ x (increasing-binseq-ℕ (succ-ℕ n))
  Eq-succ-criterion-ℕ∞↑ {x} {0} r s 0 = r
  Eq-succ-criterion-ℕ∞↑ {x} {0} r s (succ-ℕ i) =
    is-bounded-is-bounded-zero-ℕ∞↑ (shift-left-ℕ∞↑ x) i s
  Eq-succ-criterion-ℕ∞↑ {x} {succ-ℕ n} r s 0 =
    is-positive-is-strictly-bounded-below-ℕ∞↑ x (succ-ℕ n) r
  Eq-succ-criterion-ℕ∞↑ {x} {succ-ℕ n} r s (succ-ℕ i) =
    Eq-succ-criterion-ℕ∞↑ {shift-left-ℕ∞↑ x} {n} r s i

abstract
  eq-succ-criterion-ℕ∞↑ :
    {x : ℕ∞↑} {n : ℕ} →
    is-strictly-bounded-below-ℕ∞↑ n x →
    is-bounded-ℕ∞↑ x (succ-ℕ n) →
    x ＝ increasing-binseq-ℕ (succ-ℕ n)
  eq-succ-criterion-ℕ∞↑ {x} {n} r s =
    is-injective-sequence-ℕ∞↑ (eq-htpy (Eq-succ-criterion-ℕ∞↑ {x} {n} r s))
```

### If an increasing binary sequence is not in the image of the natural numbers it is infinite

```agda
module _
  (x : ℕ∞↑) (H : (n : ℕ) → x ≠ increasing-binseq-ℕ n)
  where

  abstract
    Eq-infinity-is-not-in-image-increasing-binseq-ℕ :
      sequence-ℕ∞↑ x ~ const ℕ false
    Eq-infinity-is-not-in-image-increasing-binseq-ℕ zero-ℕ =
      is-false-is-not-true (sequence-ℕ∞↑ x 0) (H 0 ∘ eq-zero-is-zero-ℕ∞↑ x)
    Eq-infinity-is-not-in-image-increasing-binseq-ℕ (succ-ℕ n) =
      is-false-is-not-true
        ( sequence-ℕ∞↑ x (succ-ℕ n))
        ( H (succ-ℕ n) ∘
          eq-succ-criterion-ℕ∞↑
            ( Eq-infinity-is-not-in-image-increasing-binseq-ℕ n))

  eq-infinity-is-not-in-image-increasing-binseq-ℕ : x ＝ infinity-ℕ∞↑
  eq-infinity-is-not-in-image-increasing-binseq-ℕ =
    eq-Eq-ℕ∞↑ Eq-infinity-is-not-in-image-increasing-binseq-ℕ

  eq-infinity-is-not-in-image-increasing-binseq-ℕ' : infinity-ℕ∞↑ ＝ x
  eq-infinity-is-not-in-image-increasing-binseq-ℕ' =
    inv eq-infinity-is-not-in-image-increasing-binseq-ℕ
```

### The extended inclusion is double negation dense

```agda
abstract
  is-double-negation-dense-increasing-binseq-Maybe-ℕ :
    is-double-negation-dense-map increasing-binseq-Maybe-ℕ
  is-double-negation-dense-increasing-binseq-Maybe-ℕ x H =
    H ( inr star ,
        eq-infinity-is-not-in-image-increasing-binseq-ℕ' x
          ( λ n p → H (inl n , inv p)))

double-negation-dense-increasing-binseq-Maybe-ℕ :
  Maybe ℕ ↠¬¬ ℕ∞↑
double-negation-dense-increasing-binseq-Maybe-ℕ =
  ( increasing-binseq-Maybe-ℕ ,
    is-double-negation-dense-increasing-binseq-Maybe-ℕ)
```

```agda
module _
  {l : Level} {Y : ℕ∞↑ → UU l}
  {f g : (x : ℕ∞↑) → Y x}
  where

  htpy-ℕ∞↑-htpy-ℕ :
    (H : (x : ℕ∞↑) → has-double-negation-stable-equality (Y x)) →
    ((n : ℕ) → f (increasing-binseq-ℕ n) ＝ g (increasing-binseq-ℕ n)) →
    f infinity-ℕ∞↑ ＝ g infinity-ℕ∞↑ →
    f ~ g
  htpy-ℕ∞↑-htpy-ℕ H h h∞ =
    htpy-htpy-double-negation-dense-map
      ( double-negation-dense-increasing-binseq-Maybe-ℕ)
      ( H)
      ( ind-Maybe (h , h∞))
```

### The tight bounds on the image of the natural numbers

```agda
is-bounded-increasing-binseq-ℕ :
  (n : ℕ) →
  is-bounded-ℕ∞↑ (increasing-binseq-ℕ n) n
is-bounded-increasing-binseq-ℕ zero-ℕ =
  refl
is-bounded-increasing-binseq-ℕ (succ-ℕ n) =
  is-bounded-increasing-binseq-ℕ n

is-strictly-bounded-below-increasing-binseq-succ-ℕ :
  (n : ℕ) →
  is-strictly-bounded-below-ℕ∞↑ n (increasing-binseq-ℕ (succ-ℕ n))
is-strictly-bounded-below-increasing-binseq-succ-ℕ zero-ℕ =
  refl
is-strictly-bounded-below-increasing-binseq-succ-ℕ (succ-ℕ n) =
  is-strictly-bounded-below-increasing-binseq-succ-ℕ n
```

## References

- [`CoNaturals.GenericConvergentSequence`](https://martinescardo.github.io/TypeTopology/CoNaturals.GenericConvergentSequence.html)
  at TypeTopology {{#cite TypeTopology}}

{{#bibliography}}
