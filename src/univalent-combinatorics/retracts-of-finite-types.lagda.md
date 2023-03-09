# Retracts of finite types

```agda
module univalent-combinatorics.retracts-of-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-embeddings
open import foundation.decidable-maps
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.fibers-of-maps
open import foundation.functoriality-propositional-truncation
open import foundation.injective-maps
open import foundation.propositional-maps
open import foundation.retractions
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-decidable-subtypes
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Properties

### If a map `i : A → Fin k` has a retraction, then it is a decidable map

```agda
is-decidable-map-retr-Fin :
  {l1 : Level} (k : ℕ) {A : UU l1} (i : A → Fin k) → retr i → is-decidable-map i
is-decidable-map-retr-Fin k =
  is-decidable-map-retr (has-decidable-equality-Fin k)
```

### If a map `i : A → B` into a finite type `B` has a retraction, then `i` is decidable and `A` is finite.

```agda
is-decidable-map-retr-count :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count B) (i : A → B) → retr i →
  is-decidable-map i
is-decidable-map-retr-count e =
  is-decidable-map-retr (has-decidable-equality-count e)

is-decidable-map-retr-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : is-finite B) (i : A → B) →
  retr i → is-decidable-map i
is-decidable-map-retr-is-finite H =
  is-decidable-map-retr (has-decidable-equality-is-finite H)
```

```agda
abstract
  is-emb-retract-count :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count B) (i : A → B) →
    retr i → is-emb i
  is-emb-retract-count e i R =
    is-emb-is-injective (is-set-count e) (is-injective-retr i R)

emb-retract-count :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count B) (i : A → B) →
  retr i → A ↪ B
pr1 (emb-retract-count e i R) = i
pr2 (emb-retract-count e i R) = is-emb-retract-count e i R

decidable-emb-retract-count :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count B) (i : A → B) →
  retr i → A ↪d B
pr1 (decidable-emb-retract-count e i R) = i
pr1 (pr2 (decidable-emb-retract-count e i R)) = is-emb-retract-count e i R
pr2 (pr2 (decidable-emb-retract-count e i R)) =
  is-decidable-map-retr-count e i R

count-retract :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → count B → count A
count-retract (pair i R) e =
  count-equiv
    ( equiv-total-fib i)
    ( count-decidable-subtype
      ( decidable-subtype-decidable-emb (decidable-emb-retract-count e i R))
      ( e))

abstract
  is-finite-retract :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} → A retract-of B →
    is-finite B → is-finite A
  is-finite-retract R = map-trunc-Prop (count-retract R)
```
