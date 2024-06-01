# Sequences in partially ordered sets

```agda
module order-theory.sequences-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.asymptotical-dependent-sequences
open import foundation.asymptotically-equal-sequences
open import foundation.binary-relations
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

### Sequences in a partially ordered sets

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
```
