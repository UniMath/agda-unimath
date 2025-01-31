# Equality of conatural numbers

```agda
{-# OPTIONS --guardedness #-}

module elementary-number-theory.equality-conatural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.conatural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coherently-invertible-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-stable-equality
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.maybe
open import foundation.negation
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.sets
open import foundation.tight-apartness-relations
open import foundation.torsorial-type-families
open import foundation.unit-type
open import foundation.universe-levels

open import logic.double-negation-elimination
```

</details>

## Idea

We characterize [equality](foundation-core.identity-types.md) of
[conatural numbers](elementary-number-theory.conatural-numbers.md) by the
following description. Two conatural numbers `x` and `y` are _equal_ if they are
both zero or, coinductively, their predecessors are equal.

Since the conaturals `ℕ∞` is a coinductive type, it does not follow from the
other postulates of agda-unimath that this description characterizes equality,
and we therefore have to postulate that it does, just as we have for functions
with [function extensionality](foundation.function-extensionality.md) and the
universe with [univalence](foundation.univalence.md).

## Definitions

### Observational equality on the conaturals

We borrow a trick from the cubical Agda library in our definition of the
observational equality predicate on conatural numbers, `Eq-ℕ∞`, so that our
definition passes Agda's termination checker.

```agda
record Eq-ℕ∞ (x y : ℕ∞) : UU lzero

Eq-Maybe-ℕ∞' : Maybe ℕ∞ → Maybe ℕ∞ → UU lzero
Eq-Maybe-ℕ∞' (inl x) (inl y) = Eq-ℕ∞ x y
Eq-Maybe-ℕ∞' (inl x) (inr _) = empty
Eq-Maybe-ℕ∞' (inr _) (inl y) = empty
Eq-Maybe-ℕ∞' (inr _) (inr _) = unit

data Eq-Maybe-ℕ∞ (x y : Maybe ℕ∞) : UU lzero where
  cons-Eq-Maybe-ℕ∞ : Eq-Maybe-ℕ∞' x y → Eq-Maybe-ℕ∞ x y

record Eq-ℕ∞ x y where
  coinductive
  constructor cons-Eq-ℕ∞
  field
    decons-Eq-ℕ∞ : Eq-Maybe-ℕ∞ (decons-ℕ∞ x) (decons-ℕ∞ y)

open Eq-ℕ∞ public
```

### Observational equality on the conaturals is reflexive

The following does not pass Agda's termination checker if we omit the
intermediate data type `Eq-Maybe-ℕ∞`.

```agda
refl-Eq-Maybe-ℕ∞ : {x : Maybe ℕ∞} → Eq-Maybe-ℕ∞ x x

refl-Eq-ℕ∞ : {x : ℕ∞} → Eq-ℕ∞ x x
decons-Eq-ℕ∞ refl-Eq-ℕ∞ = refl-Eq-Maybe-ℕ∞

refl-Eq-Maybe-ℕ∞ {inl x} = cons-Eq-Maybe-ℕ∞ refl-Eq-ℕ∞
refl-Eq-Maybe-ℕ∞ {inr x} = cons-Eq-Maybe-ℕ∞ star

refl-Eq-Maybe-ℕ∞' : {x : Maybe ℕ∞} → Eq-Maybe-ℕ∞' x x
refl-Eq-Maybe-ℕ∞' {inl x} = refl-Eq-ℕ∞
refl-Eq-Maybe-ℕ∞' {inr x} = star
```

```agda
Eq-Maybe-eq-ℕ∞ : {x y : Maybe ℕ∞} → x ＝ y → Eq-Maybe-ℕ∞ x y
Eq-Maybe-eq-ℕ∞ refl = refl-Eq-Maybe-ℕ∞

Eq-eq-ℕ∞ : {x y : ℕ∞} → x ＝ y → Eq-ℕ∞ x y
Eq-eq-ℕ∞ refl = refl-Eq-ℕ∞

Eq-Maybe-eq-ℕ∞' : {x y : Maybe ℕ∞} → x ＝ y → Eq-Maybe-ℕ∞' x y
Eq-Maybe-eq-ℕ∞' refl = refl-Eq-Maybe-ℕ∞'
```

## Postulates

We postulate that the map `Eq-eq-ℕ∞ : x ＝ y → Eq-ℕ∞ x y` is a
[coherently invertible map](foundation-core.coherently-invertible-maps.md).

```agda
module _
  {x y : ℕ∞}
  where

  postulate
    eq-Eq-ℕ∞ : Eq-ℕ∞ x y → x ＝ y

  postulate
    is-section-eq-Eq-ℕ∞ : is-section Eq-eq-ℕ∞ eq-Eq-ℕ∞

  postulate
    is-retraction-eq-Eq-ℕ∞ : is-retraction Eq-eq-ℕ∞ eq-Eq-ℕ∞

  postulate
    coh-eq-Eq-ℕ∞ :
      coherence-is-coherently-invertible
        ( Eq-eq-ℕ∞)
        ( eq-Eq-ℕ∞)
        ( is-section-eq-Eq-ℕ∞)
        ( is-retraction-eq-Eq-ℕ∞)
```

## Further definitions

```agda
module _ {x y : ℕ∞}
  where

  is-coherently-invertible-Eq-eq-ℕ∞ :
    is-coherently-invertible (Eq-eq-ℕ∞ {x} {y})
  is-coherently-invertible-Eq-eq-ℕ∞ =
    ( eq-Eq-ℕ∞ ,
      is-section-eq-Eq-ℕ∞ ,
      is-retraction-eq-Eq-ℕ∞ ,
      coh-eq-Eq-ℕ∞)

  is-equiv-Eq-eq-ℕ∞ : is-equiv (Eq-eq-ℕ∞ {x} {y})
  is-equiv-Eq-eq-ℕ∞ =
    is-equiv-is-invertible
      eq-Eq-ℕ∞
      is-section-eq-Eq-ℕ∞
      is-retraction-eq-Eq-ℕ∞

  is-equiv-eq-Eq-ℕ∞ : is-equiv (eq-Eq-ℕ∞ {x} {y})
  is-equiv-eq-Eq-ℕ∞ =
    is-equiv-is-invertible
      Eq-eq-ℕ∞
      is-retraction-eq-Eq-ℕ∞
      is-section-eq-Eq-ℕ∞

  equiv-Eq-eq-ℕ∞ : (x ＝ y) ≃ Eq-ℕ∞ x y
  equiv-Eq-eq-ℕ∞ = Eq-eq-ℕ∞ , is-equiv-Eq-eq-ℕ∞

  equiv-eq-Eq-ℕ∞ : Eq-ℕ∞ x y ≃ (x ＝ y)
  equiv-eq-Eq-ℕ∞ = eq-Eq-ℕ∞ , is-equiv-eq-Eq-ℕ∞

is-torsorial-Eq-ℕ∞ :
  {l1 l2 : Level} {x : ℕ∞} →
  is-torsorial (Eq-ℕ∞ x)
is-torsorial-Eq-ℕ∞ =
  fundamental-theorem-id'
    ( λ _ → Eq-eq-ℕ∞)
    ( λ _ → is-equiv-Eq-eq-ℕ∞)
```

## Properties

### The deconstructor function on the conaturals is injective

```agda
Eq-eq-decons-ℕ∞ : {x y : ℕ∞} → decons-ℕ∞ x ＝ decons-ℕ∞ y → Eq-ℕ∞ x y
Eq-eq-decons-ℕ∞ = cons-Eq-ℕ∞ ∘ Eq-Maybe-eq-ℕ∞

is-injective-decons-ℕ∞ : is-injective decons-ℕ∞
is-injective-decons-ℕ∞ = eq-Eq-ℕ∞ ∘ Eq-eq-decons-ℕ∞
```

### The conaturals are a fixed point of the Maybe monad

```agda
is-retraction-cons-ℕ∞ : is-retraction decons-ℕ∞ cons-ℕ∞
is-retraction-cons-ℕ∞ x =
  is-injective-decons-ℕ∞ (is-section-cons-ℕ∞ (decons-ℕ∞ x))

is-equiv-cons-ℕ∞ : is-equiv cons-ℕ∞
is-equiv-cons-ℕ∞ =
  is-equiv-is-invertible decons-ℕ∞ is-retraction-cons-ℕ∞ is-section-cons-ℕ∞

is-equiv-decons-ℕ∞ : is-equiv decons-ℕ∞
is-equiv-decons-ℕ∞ =
  is-equiv-is-invertible cons-ℕ∞ is-section-cons-ℕ∞ is-retraction-cons-ℕ∞

compute-Maybe-ℕ∞ : Maybe ℕ∞ ≃ ℕ∞
compute-Maybe-ℕ∞ = (cons-ℕ∞ , is-equiv-cons-ℕ∞)

compute-Maybe-ℕ∞' : ℕ∞ ≃ Maybe ℕ∞
compute-Maybe-ℕ∞' = (decons-ℕ∞ , is-equiv-decons-ℕ∞)
```

### The equality predicates on `Maybe ℕ∞` agree

```agda
module _
  {x y : Maybe ℕ∞}
  where

  decons-Eq-Maybe-ℕ∞ : Eq-Maybe-ℕ∞ x y → Eq-Maybe-ℕ∞' x y
  decons-Eq-Maybe-ℕ∞ (cons-Eq-Maybe-ℕ∞ x) = x

  is-retraction-decons-Eq-Maybe-ℕ∞ :
    is-retraction cons-Eq-Maybe-ℕ∞ decons-Eq-Maybe-ℕ∞
  is-retraction-decons-Eq-Maybe-ℕ∞ = refl-htpy

  is-section-decons-Eq-Maybe-ℕ∞ :
    is-section cons-Eq-Maybe-ℕ∞ decons-Eq-Maybe-ℕ∞
  is-section-decons-Eq-Maybe-ℕ∞ (cons-Eq-Maybe-ℕ∞ p) = refl

  is-equiv-cons-Eq-Maybe-ℕ∞ : is-equiv cons-Eq-Maybe-ℕ∞
  is-equiv-cons-Eq-Maybe-ℕ∞ =
    is-equiv-is-invertible
      ( decons-Eq-Maybe-ℕ∞)
      ( is-section-decons-Eq-Maybe-ℕ∞)
      ( is-retraction-decons-Eq-Maybe-ℕ∞)

  is-equiv-decons-Eq-Maybe-ℕ∞ : is-equiv decons-Eq-Maybe-ℕ∞
  is-equiv-decons-Eq-Maybe-ℕ∞ =
    is-equiv-is-invertible
      ( cons-Eq-Maybe-ℕ∞)
      ( is-retraction-decons-Eq-Maybe-ℕ∞)
      ( is-section-decons-Eq-Maybe-ℕ∞)

  compute-Eq-Maybe-ℕ∞ : Eq-Maybe-ℕ∞' x y ≃ Eq-Maybe-ℕ∞ x y
  compute-Eq-Maybe-ℕ∞ = (cons-Eq-Maybe-ℕ∞ , is-equiv-cons-Eq-Maybe-ℕ∞)

  inv-compute-Eq-Maybe-ℕ∞ : Eq-Maybe-ℕ∞ x y ≃ Eq-Maybe-ℕ∞' x y
  inv-compute-Eq-Maybe-ℕ∞ =
    ( decons-Eq-Maybe-ℕ∞ , is-equiv-decons-Eq-Maybe-ℕ∞)
```

### The equality predicate on `Maybe ℕ∞` is a retract of the equality predicate on `ℕ∞`

```agda
is-retraction-decons-Eq-ℕ∞ :
  {x y : ℕ∞} → is-retraction (cons-Eq-ℕ∞ {x} {y}) decons-Eq-ℕ∞
is-retraction-decons-Eq-ℕ∞ = refl-htpy

is-injective-cons-Eq-ℕ∞ :
  {x y : ℕ∞} → is-injective (cons-Eq-ℕ∞ {x} {y})
is-injective-cons-Eq-ℕ∞ {x} {y} =
  is-injective-has-retraction cons-Eq-ℕ∞ decons-Eq-ℕ∞
    ( is-retraction-decons-Eq-ℕ∞ {x} {y})

retraction-cons-Eq-ℕ∞ : {x y : ℕ∞} → retraction (cons-Eq-ℕ∞ {x} {y})
retraction-cons-Eq-ℕ∞ {x} {y} =
  (decons-Eq-ℕ∞ , is-retraction-decons-Eq-ℕ∞ {x} {y})

retract-compute-Eq-ℕ∞' :
  {x y : ℕ∞} → (Eq-Maybe-ℕ∞ (decons-ℕ∞ x) (decons-ℕ∞ y)) retract-of (Eq-ℕ∞ x y)
retract-compute-Eq-ℕ∞' = (cons-Eq-ℕ∞ , retraction-cons-Eq-ℕ∞)
```

### The conatural numbers have double negation stable equality

```agda
eq-Eq-Maybe-ℕ∞ : {x y : Maybe ℕ∞} → Eq-Maybe-ℕ∞ x y → x ＝ y
eq-Eq-Maybe-ℕ∞ {inl x} {inl y} p =
  ap decons-ℕ∞ (eq-Eq-ℕ∞ (cons-Eq-ℕ∞ {succ-ℕ∞ x} {succ-ℕ∞ y} p))
eq-Eq-Maybe-ℕ∞ {inl x} {inr _} (cons-Eq-Maybe-ℕ∞ ())
eq-Eq-Maybe-ℕ∞ {inr _} {inl y} (cons-Eq-Maybe-ℕ∞ ())
eq-Eq-Maybe-ℕ∞ {inr _} {inr _} p = refl
```

```agda
double-negation-elim-Eq-Maybe-ℕ∞ :
  {x y : Maybe ℕ∞} → has-double-negation-elim (Eq-Maybe-ℕ∞ x y)

double-negation-elim-Eq-ℕ∞ : {x y : ℕ∞} → has-double-negation-elim (Eq-ℕ∞ x y)
decons-Eq-ℕ∞ (double-negation-elim-Eq-ℕ∞ p) =
  double-negation-elim-Eq-Maybe-ℕ∞ (map-double-negation decons-Eq-ℕ∞ p)

double-negation-elim-Eq-Maybe-ℕ∞ {inl x} {inl y} p =
  cons-Eq-Maybe-ℕ∞
    ( double-negation-elim-Eq-ℕ∞ {x} {y}
      ( map-double-negation (Eq-eq-ℕ∞ ∘ is-injective-inl ∘ eq-Eq-Maybe-ℕ∞) p))
double-negation-elim-Eq-Maybe-ℕ∞ {inl x} {inr _} p =
  cons-Eq-Maybe-ℕ∞ (p decons-Eq-Maybe-ℕ∞)
double-negation-elim-Eq-Maybe-ℕ∞ {inr _} {inl x} p =
  cons-Eq-Maybe-ℕ∞ (p decons-Eq-Maybe-ℕ∞)
double-negation-elim-Eq-Maybe-ℕ∞ {inr _} {inr _} p =
  cons-Eq-Maybe-ℕ∞ star

has-double-negation-stable-equality-ℕ∞ : has-double-negation-stable-equality ℕ∞
has-double-negation-stable-equality-ℕ∞ x y p =
  eq-Eq-ℕ∞ (double-negation-elim-Eq-ℕ∞ (map-double-negation Eq-eq-ℕ∞ p))
```

### The type of conaturals is a set

```agda
is-set-ℕ∞ : is-set ℕ∞
is-set-ℕ∞ =
  is-set-has-double-negation-stable-equality
    ( has-double-negation-stable-equality-ℕ∞)
```

### The type of conaturals has a tight apartness relation

> Agda's termination checker is unhappy with the following proof.

```text
cases-is-cotransitive-Eq-Maybe-ℕ∞ :
  (x y z : Maybe ℕ∞) →
  ¬ (Eq-Maybe-ℕ∞ x y) → ¬ (Eq-Maybe-ℕ∞ x z) + ¬ (Eq-Maybe-ℕ∞ z y)

cases-is-cotransitive-Eq-ℕ∞ :
  (x y z : ℕ∞) → ¬ (Eq-ℕ∞ x y) → ¬ (Eq-ℕ∞ x z) + ¬ (Eq-ℕ∞ z y)
cases-is-cotransitive-Eq-ℕ∞ x y z np with
  cases-is-cotransitive-Eq-Maybe-ℕ∞
    ( decons-ℕ∞ x)
    ( decons-ℕ∞ y)
    ( decons-ℕ∞ z)
    ( map-neg cons-Eq-ℕ∞ np)
... | (inl nx) = inl (map-neg (Eq-Maybe-eq-ℕ∞ ∘ ap decons-ℕ∞ ∘ eq-Eq-ℕ∞) nx)
... | (inr ny) = inr (map-neg (Eq-Maybe-eq-ℕ∞ ∘ ap decons-ℕ∞ ∘ eq-Eq-ℕ∞) ny)

cases-is-cotransitive-Eq-Maybe-ℕ∞ (inl x) (inl y) (inl z) np with
  cases-is-cotransitive-Eq-ℕ∞ x y z (map-neg cons-Eq-Maybe-ℕ∞ np)
... | (inl nx) = inl (map-neg (Eq-eq-ℕ∞ ∘ is-injective-inl ∘ eq-Eq-Maybe-ℕ∞) nx)
... | (inr ny) = inr (map-neg (Eq-eq-ℕ∞ ∘ is-injective-inl ∘ eq-Eq-Maybe-ℕ∞) ny)
cases-is-cotransitive-Eq-Maybe-ℕ∞ (inl x) (inl y) (inr z) np =
  inl (map-neg decons-Eq-Maybe-ℕ∞ id)
cases-is-cotransitive-Eq-Maybe-ℕ∞ (inl x) (inr y) (inl z) np =
  inr (map-neg decons-Eq-Maybe-ℕ∞ id)
cases-is-cotransitive-Eq-Maybe-ℕ∞ (inl x) (inr y) (inr z) np =
  inl (map-neg decons-Eq-Maybe-ℕ∞ id)
cases-is-cotransitive-Eq-Maybe-ℕ∞ (inr x) y (inl z) np =
  inl (map-neg decons-Eq-Maybe-ℕ∞ id)
cases-is-cotransitive-Eq-Maybe-ℕ∞ (inr x) (inl y) (inr z) np =
  inr (map-neg decons-Eq-Maybe-ℕ∞ id)
cases-is-cotransitive-Eq-Maybe-ℕ∞ (inr x) (inr y) (inr z) np =
  ex-falso (np (cons-Eq-Maybe-ℕ∞ star))
```
