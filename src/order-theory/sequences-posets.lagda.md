# Sequences in partially ordered sets

```agda
module order-theory.sequences-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.asymptotical-dependent-sequences
open import foundation.asymptotically-constant-sequences
open import foundation.asymptotically-equal-sequences
open import foundation.binary-relations
open import foundation.constant-sequences
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.universe-levels

open import order-theory.posets
```

</details>

## Idea

Sequences in a partially ordered set are sequences in the underlying set. They
can be partially ordered by pointwise comparison.

## Definitions

### Sequences in partially ordered sets

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  sequence-poset : UU l1
  sequence-poset = sequence (type-Poset P)
```

### Pointwise comparison on sequences in partially ordered sets

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u v : sequence-poset P)
  where

  leq-value-prop-sequence-poset : ℕ → Prop l2
  leq-value-prop-sequence-poset n = leq-Poset-Prop P (u n) (v n)

  leq-value-sequence-poset : ℕ → UU l2
  leq-value-sequence-poset = type-Prop ∘ leq-value-prop-sequence-poset

  leq-prop-sequence-poset : Prop l2
  leq-prop-sequence-poset = Π-Prop ℕ leq-value-prop-sequence-poset

  leq-sequence-poset : UU l2
  leq-sequence-poset = type-Prop leq-prop-sequence-poset

  is-prop-leq-sequence-poset : is-prop leq-sequence-poset
  is-prop-leq-sequence-poset = is-prop-type-Prop leq-prop-sequence-poset
```

### The partially ordered set of sequences in a partially ordered set

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  poset-sequence-poset : Poset l1 l2
  pr1 (pr1 poset-sequence-poset) = sequence-poset P
  pr1 (pr2 (pr1 poset-sequence-poset)) = leq-prop-sequence-poset P
  pr1 (pr2 (pr2 (pr1 poset-sequence-poset))) u n = refl-leq-Poset P (u n)
  pr2 (pr2 (pr2 (pr1 poset-sequence-poset))) u v w J I n =
    transitive-leq-Poset P (u n) (v n) (w n) (J n) (I n)
  pr2 poset-sequence-poset u v I J =
    eq-sequence u v (λ n → antisymmetric-leq-Poset P (u n) (v n) (I n) (J n))

  refl-leq-sequence-poset : is-reflexive (leq-sequence-poset P)
  refl-leq-sequence-poset = refl-leq-Poset poset-sequence-poset

  transitive-leq-sequence-poset : is-transitive (leq-sequence-poset P)
  transitive-leq-sequence-poset = transitive-leq-Poset poset-sequence-poset

  antisymmetric-leq-sequence-poset : is-antisymmetric (leq-sequence-poset P)
  antisymmetric-leq-sequence-poset =
    antisymmetric-leq-Poset poset-sequence-poset
```

### Asymptotical inequality of sequences in partially ordered sets

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  leq-∞-sequence-poset : (u v : sequence-poset P) → UU l2
  leq-∞-sequence-poset u v = asymptotically (leq-value-sequence-poset P u v)

  refl-leq-∞-sequence-poset : is-reflexive leq-∞-sequence-poset
  refl-leq-∞-sequence-poset = asymptotically-Π ∘ (refl-leq-sequence-poset P)

  leq-∞-eq-∞-sequence-poset :
    {u v : sequence-poset P} → eq-∞-sequence u v → leq-∞-sequence-poset u v
  leq-∞-eq-∞-sequence-poset {u} {v} =
    map-asymptotically-Π (λ n → leq-eq-Poset P)

  transitive-leq-∞-sequence-poset : is-transitive leq-∞-sequence-poset
  transitive-leq-∞-sequence-poset u v w =
    map-binary-asymptotically-Π (λ n → transitive-leq-Poset P (u n) (v n) (w n))

  antisymmetric-∞-leq-∞-sequence-poset :
    (u v : sequence-poset P) →
    leq-∞-sequence-poset u v →
    leq-∞-sequence-poset v u →
    eq-∞-sequence u v
  antisymmetric-∞-leq-∞-sequence-poset u v =
    map-binary-asymptotically-Π (λ n → antisymmetric-leq-Poset P (u n) (v n))

  leq-∞-leq-sequence-poset :
    {u v : sequence-poset P} →
    leq-sequence-poset P u v →
    leq-∞-sequence-poset u v
  leq-∞-leq-sequence-poset = asymptotically-Π
```

### Concatenation of asymptotical inequality and equality of sequences in partially ordered sets

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {u v w : sequence-poset P}
  where

  concatenate-eq-∞-leq-∞-sequence-poset :
    eq-∞-sequence u v → leq-∞-sequence-poset P v w → leq-∞-sequence-poset P u w
  concatenate-eq-∞-leq-∞-sequence-poset =
    map-binary-asymptotically-Π (λ n → concatenate-eq-leq-Poset P)

  concatenate-leq-∞-eq-∞-sequence-poset :
    leq-∞-sequence-poset P u v → eq-∞-sequence v w → leq-∞-sequence-poset P u w
  concatenate-leq-∞-eq-∞-sequence-poset =
    map-binary-asymptotically-Π (λ n → concatenate-leq-eq-Poset P)

module _
  {l1 l2 : Level} (P : Poset l1 l2) {u v w z : sequence-poset P}
  where

  concatenate-eq-∞-leq-∞-eq-∞-sequence-poset :
    eq-∞-sequence u v →
    leq-∞-sequence-poset P v w →
    eq-∞-sequence w z →
    leq-∞-sequence-poset P u z
  concatenate-eq-∞-leq-∞-eq-∞-sequence-poset =
    ( map-binary-asymptotically) ∘
    ( map-asymptotically-Π
      ( λ n H J →
        (concatenate-eq-leq-Poset P H) ∘ (concatenate-leq-eq-Poset P J)))
```

## Properties

### Asymptotical values preserves asymptotical inequality of sequences in partially ordered sets

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u v : sequence-poset P)
  (I : leq-∞-sequence-poset P u v)
  where

  leq-∞-left-leq-∞-constant-sequence-poset :
    (H : is-∞-constant-sequence u) →
    leq-∞-sequence-poset P (const-∞-value-∞-constant-sequence H) v
  leq-∞-left-leq-∞-constant-sequence-poset H =
    concatenate-eq-∞-leq-∞-sequence-poset
      ( P)
      ( eq-∞-value-∞-constant-sequence H)
      ( I)

  leq-∞-right-leq-∞-constant-sequence-poset :
    (H : is-∞-constant-sequence v) →
    leq-∞-sequence-poset P u (const-∞-value-∞-constant-sequence H)
  leq-∞-right-leq-∞-constant-sequence-poset =
    ( concatenate-leq-∞-eq-∞-sequence-poset P I) ∘
    ( eq-∞-value-∞-constant-sequence')

  leq-∞-value-leq-∞-constant-sequence-poset :
    (H : is-∞-constant-sequence u) →
    (K : is-∞-constant-sequence v) →
    leq-∞-sequence-poset P
      (const-∞-value-∞-constant-sequence H)
      (const-∞-value-∞-constant-sequence K)
  leq-∞-value-leq-∞-constant-sequence-poset H K =
    concatenate-eq-∞-leq-∞-eq-∞-sequence-poset
      ( P)
      ( eq-∞-value-∞-constant-sequence H)
      ( I)
      ( eq-∞-value-∞-constant-sequence' K)

  leq-value-leq-∞-constant-sequence-poset :
    (H : is-∞-constant-sequence u) →
    (K : is-∞-constant-sequence v) →
    leq-Poset P (∞-value-∞-constant-sequence H) (∞-value-∞-constant-sequence K)
  leq-value-leq-∞-constant-sequence-poset H K =
    value-∞-asymptotically (leq-∞-value-leq-∞-constant-sequence-poset H K)
```

### A sequence in a partially ordered set that asymptotically lies between two asymptotically equal sequences is asymptotically equal to them

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u v w : sequence-poset P)
  (I : leq-∞-sequence-poset P u v) (J : leq-∞-sequence-poset P v w)
  (E : eq-∞-sequence w u)
  where

  left-eq-∞-guarded-sequence-poset : eq-∞-sequence u v
  left-eq-∞-guarded-sequence-poset =
    antisymmetric-∞-leq-∞-sequence-poset
      ( P)
      ( u)
      ( v)
      ( I)
      ( concatenate-leq-∞-eq-∞-sequence-poset P J E)

  right-eq-∞-guarded-sequence-poset : eq-∞-sequence v w
  right-eq-∞-guarded-sequence-poset =
    antisymmetric-∞-leq-∞-sequence-poset
      ( P)
      ( v)
      ( w)
      ( J)
      ( concatenate-eq-∞-leq-∞-sequence-poset P E I)
```

### A sequence in a partially ordered that asymptotically lies between two asymptotically constant sequences with the same asymptotical value is asymptotically constant

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u v w : sequence-poset P)
  (I : leq-∞-sequence-poset P u v) (J : leq-∞-sequence-poset P v w)
  (H : is-∞-constant-sequence u) (K : is-∞-constant-sequence w)
  where

  ∞-constant-eq-∞-value-guarded-sequence-poset :
    Id
      (∞-value-∞-constant-sequence K)
      (∞-value-∞-constant-sequence H) →
    is-∞-constant-sequence v
  ∞-constant-eq-∞-value-guarded-sequence-poset E =
    preserves-∞-constant-eq-∞-sequence u v
      ( left-eq-∞-guarded-sequence-poset P u v w I J
        ( eq-∞-sequence-eq-∞-value-∞-constant-sequence w u K H E))
      ( H)

  ∞-constant-leq-∞-value-guarded-sequence-poset :
    leq-Poset P
      (∞-value-∞-constant-sequence K)
      (∞-value-∞-constant-sequence H) →
    is-∞-constant-sequence v
  ∞-constant-leq-∞-value-guarded-sequence-poset E =
    ∞-constant-eq-∞-value-guarded-sequence-poset
      ( antisymmetric-leq-Poset
        ( P)
        ( ∞-value-∞-constant-sequence K)
        ( ∞-value-∞-constant-sequence H)
        ( E)
        ( leq-value-leq-∞-constant-sequence-poset
          ( P)
          ( u)
          ( w)
          ( transitive-leq-∞-sequence-poset P u v w J I)
          ( H)
          ( K)))
```
