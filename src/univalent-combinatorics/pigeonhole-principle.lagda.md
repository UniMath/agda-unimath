# The pigeonhole principle

```agda
module univalent-combinatorics.pigeonhole-principle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.noninjective-maps
open import foundation.pairs-of-distinct-elements
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import univalent-combinatorics.counting
open import univalent-combinatorics.embeddings-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.repetitions-of-values
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a map `f : X → Y` between
[finite types](univalent-combinatorics.finite-types.md) with `k` and `l`
elements respectively, then if `f` is
[injective](foundation-core.injective-maps.md), `k` is
[less than or equal](elementary-number-theory.inequality-natural-numbers.md) to
`l`. Conversely, if `l` is
[less than](elementary-number-theory.strict-inequality-natural-numbers.md) `k`,
the map `f` [repeats a value](foundation.repetitions-of-values.md), meaning it
is [noninjective](foundation.noninjective-maps.md).

## Theorems

### The pigeonhole principle for standard finite types

#### Given an embedding `Fin k ↪ Fin l`, it follows that `k ≤ l`

```agda
leq-emb-Fin :
  (k l : ℕ) → (Fin k ↪ Fin l) → k ≤-ℕ l
leq-emb-Fin 0 0 f = refl-leq-ℕ 0
leq-emb-Fin (succ-ℕ k) 0 f = map-emb f (inr star)
leq-emb-Fin 0 (succ-ℕ l) f = leq-zero-ℕ (succ-ℕ l)
leq-emb-Fin (succ-ℕ k) (succ-ℕ l) f = leq-emb-Fin k l (reduce-emb-Fin k l f)

leq-is-emb-Fin :
  (k l : ℕ) {f : Fin k → Fin l} → is-emb f → k ≤-ℕ l
leq-is-emb-Fin k l {f = f} H = leq-emb-Fin k l (f , H)
```

#### Given an injective map `Fin k → Fin l`, it follows that `k ≤ l`

```agda
leq-is-injective-Fin :
  (k l : ℕ) {f : Fin k → Fin l} → is-injective f → k ≤-ℕ l
leq-is-injective-Fin k l H =
  leq-is-emb-Fin k l (is-emb-is-injective (is-set-Fin l) H)
```

#### If `l < k`, then any map `f : Fin k → Fin l` is not an embedding

```agda
is-not-emb-le-Fin :
  (k l : ℕ) (f : Fin k → Fin l) → l <-ℕ k → ¬ (is-emb f)
is-not-emb-le-Fin k l f p =
  map-neg (leq-is-emb-Fin k l) (contradiction-le-ℕ l k p)
```

#### If `l < k`, then any map `f : Fin k → Fin l` is not injective

```agda
is-not-injective-le-Fin :
  (k l : ℕ) (f : Fin k → Fin l) → l <-ℕ k → is-not-injective f
is-not-injective-le-Fin k l f p =
  map-neg (is-emb-is-injective (is-set-Fin l)) (is-not-emb-le-Fin k l f p)
```

#### There is no injective map `Fin (k + 1) → Fin k`

```agda
is-not-injective-map-Fin-succ-Fin :
  (k : ℕ) (f : Fin (succ-ℕ k) → Fin k) → is-not-injective f
is-not-injective-map-Fin-succ-Fin k f =
  is-not-injective-le-Fin (succ-ℕ k) k f (succ-le-ℕ k)
```

#### There is no embedding `ℕ ↪ Fin k`

```agda
no-embedding-ℕ-Fin :
  (k : ℕ) → ¬ (ℕ ↪ Fin k)
no-embedding-ℕ-Fin k e =
  contradiction-leq-ℕ k k
    ( refl-leq-ℕ k)
    ( leq-emb-Fin (succ-ℕ k) k (comp-emb e (emb-nat-Fin (succ-ℕ k))))
```

#### For any `f : Fin k → Fin l`, where `l < k`, we construct a pair of distinct elements of `Fin k` on which `f` assumes the same value

```agda
module _
  (k l : ℕ) (f : Fin k → Fin l) (p : l <-ℕ k)
  where

  repetition-of-values-le-Fin : repetition-of-values f
  repetition-of-values-le-Fin =
    repetition-of-values-is-not-injective-Fin k l f
      ( is-not-injective-le-Fin k l f p)

  pair-of-distinct-elements-repetition-of-values-le-Fin :
    pair-of-distinct-elements (Fin k)
  pair-of-distinct-elements-repetition-of-values-le-Fin =
    pr1 repetition-of-values-le-Fin

  first-repetition-of-values-le-Fin : Fin k
  first-repetition-of-values-le-Fin =
    first-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-of-values-le-Fin

  second-repetition-of-values-le-Fin : Fin k
  second-repetition-of-values-le-Fin =
    second-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-of-values-le-Fin

  distinction-repetition-of-values-le-Fin :
    first-repetition-of-values-le-Fin ≠ second-repetition-of-values-le-Fin
  distinction-repetition-of-values-le-Fin =
    distinction-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-of-values-le-Fin

  is-repetition-of-values-repetition-of-values-le-Fin :
    is-repetition-of-values f
      pair-of-distinct-elements-repetition-of-values-le-Fin
  is-repetition-of-values-repetition-of-values-le-Fin =
    is-repetition-of-values-repetition-of-values f
      repetition-of-values-le-Fin

  is-noninjective-le-Fin : is-noninjective f
  is-noninjective-le-Fin = unit-trunc-Prop repetition-of-values-le-Fin

repetition-of-values-Fin-succ-to-Fin :
  (k : ℕ) (f : Fin (succ-ℕ k) → Fin k) → repetition-of-values f
repetition-of-values-Fin-succ-to-Fin k f =
  repetition-of-values-le-Fin (succ-ℕ k) k f (succ-le-ℕ k)

is-noninjective-Fin-succ-to-Fin :
  (k : ℕ) (f : Fin (succ-ℕ k) → Fin k) → is-noninjective f
is-noninjective-Fin-succ-to-Fin k f =
  unit-trunc-Prop (repetition-of-values-Fin-succ-to-Fin k f)
```

### The pigeonhole principle for types equipped with a counting

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (eA : count A) (eB : count B)
  where
```

#### If `f : A ↪ B` is an embedding between types equipped with a counting, then the number of elements of `A` is less than the number of elements of `B`

```agda
  leq-emb-count :
    (A ↪ B) → (number-of-elements-count eA) ≤-ℕ (number-of-elements-count eB)
  leq-emb-count f =
    leq-emb-Fin
      ( number-of-elements-count eA)
      ( number-of-elements-count eB)
      ( comp-emb
        ( comp-emb (emb-equiv (inv-equiv-count eB)) f)
        ( emb-equiv (equiv-count eA)))

  leq-is-emb-count :
    {f : A → B} → is-emb f →
    number-of-elements-count eA ≤-ℕ number-of-elements-count eB
  leq-is-emb-count {f} H = leq-emb-count (f , H)
```

#### If `f : A → B` is an injective map between types equipped with a counting, then the number of elements of `A` is less than the number of elements of `B`

```agda
  leq-is-injective-count :
    {f : A → B} → is-injective f →
    number-of-elements-count eA ≤-ℕ number-of-elements-count eB
  leq-is-injective-count H =
    leq-is-emb-count (is-emb-is-injective (is-set-count eB) H)
```

#### There is no embedding `A ↪ B` between types equipped with a counting if the number of elements of `B` is strictly less than the number of elements of `A`

```agda
  is-not-emb-le-count :
    (f : A → B) →
    number-of-elements-count eB <-ℕ number-of-elements-count eA →
    ¬ (is-emb f)
  is-not-emb-le-count f p H =
    is-not-emb-le-Fin
      ( number-of-elements-count eA)
      ( number-of-elements-count eB)
      ( map-emb h)
      ( p)
      ( is-emb-map-emb h)
    where
    h : Fin (number-of-elements-count eA) ↪ Fin (number-of-elements-count eB)
    h = comp-emb
        ( emb-equiv (inv-equiv-count eB))
        ( comp-emb (f , H) (emb-equiv (equiv-count eA)))
```

#### There is no injective map `A → B` between types equipped with a counting if the number of elements of `B` is strictly less than the number of elements of `A`

```agda
  is-not-injective-le-count :
    (f : A → B) →
    number-of-elements-count eB <-ℕ number-of-elements-count eA →
    is-not-injective f
  is-not-injective-le-count f p H =
    is-not-emb-le-count f p (is-emb-is-injective (is-set-count eB) H)
```

#### There is no embedding `ℕ ↪ A` into a type equipped with a counting

```agda
no-embedding-ℕ-count :
  {l : Level} {A : UU l} → count A → ¬ (ℕ ↪ A)
no-embedding-ℕ-count e f =
  no-embedding-ℕ-Fin
    ( number-of-elements-count e)
    ( comp-emb (emb-equiv (inv-equiv-count e)) f)
```

#### For any map `f : A → B` between types equipped with a counting, if `|A| < |B|` then we construct a pair of distinct elements of `A` on which `f` assumes the same value

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (eA : count A) (eB : count B)
  (f : A → B)
  (p : number-of-elements-count eB <-ℕ number-of-elements-count eA)
  where

  repetition-of-values-le-count : repetition-of-values f
  repetition-of-values-le-count =
    map-equiv-repetition-of-values
      ( map-inv-equiv-count eB ∘ f ∘ map-equiv-count eA)
      ( f)
      ( equiv-count eA)
      ( equiv-count eB)
      ( is-section-map-inv-equiv-count eB ·r (f ∘ (map-equiv-count eA)))
      ( repetition-of-values-le-Fin
        ( number-of-elements-count eA)
        ( number-of-elements-count eB)
        ( (map-inv-equiv-count eB ∘ f) ∘ (map-equiv-count eA))
        ( p))

  pair-of-distinct-elements-repetition-of-values-le-count :
    pair-of-distinct-elements A
  pair-of-distinct-elements-repetition-of-values-le-count =
    pr1 repetition-of-values-le-count

  first-repetition-of-values-le-count : A
  first-repetition-of-values-le-count =
    first-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-of-values-le-count

  second-repetition-of-values-le-count : A
  second-repetition-of-values-le-count =
    second-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-of-values-le-count

  distinction-repetition-of-values-le-count :
    first-repetition-of-values-le-count ≠ second-repetition-of-values-le-count
  distinction-repetition-of-values-le-count =
    distinction-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-of-values-le-count

  is-repetition-of-values-repetition-of-values-le-count :
    is-repetition-of-values f
      pair-of-distinct-elements-repetition-of-values-le-count
  is-repetition-of-values-repetition-of-values-le-count =
    is-repetition-of-values-repetition-of-values f
      repetition-of-values-le-count
```

### The pigeonhole principle for finite types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : is-finite A) (K : is-finite B)
  where
```

#### If `A ↪ B` is an embedding between finite types, then `|A| ≤ |B|`

```agda
  leq-emb-is-finite :
    (A ↪ B) →
    number-of-elements-is-finite H ≤-ℕ number-of-elements-is-finite K
  leq-emb-is-finite f =
    let
      open
        do-syntax-trunc-Prop
          ( leq-ℕ-Prop
            ( number-of-elements-is-finite H)
            ( number-of-elements-is-finite K))
    in do
      eA ← H
      eB ← K
      concatenate-eq-leq-eq-ℕ
        ( inv (compute-number-of-elements-is-finite eA H))
        ( leq-emb-count eA eB f)
        ( compute-number-of-elements-is-finite eB K)

  leq-is-emb-is-finite :
    {f : A → B} → is-emb f →
    number-of-elements-is-finite H ≤-ℕ number-of-elements-is-finite K
  leq-is-emb-is-finite {f} H = leq-emb-is-finite (f , H)
```

#### If `A → B` is an injective map between finite types, then `|A| ≤ |B|`

```agda
  leq-is-injective-is-finite :
    {f : A → B} → is-injective f →
    number-of-elements-is-finite H ≤-ℕ number-of-elements-is-finite K
  leq-is-injective-is-finite I =
    leq-is-emb-is-finite (is-emb-is-injective (is-set-is-finite K) I)
```

#### There are no embeddings between finite types `A` and `B` such that `|B| < |A|`

```agda
  is-not-emb-le-is-finite :
    (f : A → B) →
    number-of-elements-is-finite K <-ℕ number-of-elements-is-finite H →
    ¬ (is-emb f)
  is-not-emb-le-is-finite f p E =
    let open do-syntax-trunc-Prop empty-Prop
    in do
      e ← H
      d ← K
      is-not-emb-le-count e d f
        ( concatenate-eq-le-eq-ℕ
          ( compute-number-of-elements-is-finite d K)
          ( p)
          ( inv (compute-number-of-elements-is-finite e H)))
        ( E)
```

#### There are no injective maps between finite types `A` and `B` such that `|B| < |A|`

```agda
  is-not-injective-le-is-finite :
    (f : A → B) →
    number-of-elements-is-finite K <-ℕ number-of-elements-is-finite H →
    is-not-injective f
  is-not-injective-le-is-finite f p I =
    is-not-emb-le-is-finite f p (is-emb-is-injective (is-set-is-finite K) I)
```

#### There are no embeddings `ℕ ↪ A` into a finite type `A`

```agda
no-embedding-ℕ-is-finite :
  {l : Level} {A : UU l} (H : is-finite A) → ¬ (ℕ ↪ A)
no-embedding-ℕ-is-finite H f =
  apply-universal-property-trunc-Prop H empty-Prop
    ( λ e → no-embedding-ℕ-count e f)
```

## See also

- [Sequences of elements in finite types](univalent-combinatorics.sequences-finite-types.md)
