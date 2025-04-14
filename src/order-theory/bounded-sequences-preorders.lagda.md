# Bounded sequences in preorders

```agda
module order-theory.bounded-sequences-preorders where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.subsequences
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.preorders
open import order-theory.sequences-preorders
open import order-theory.subpreorders
```

</details>

## Idea

A [sequence in a preorder](order-theory.sequences-preorders.md) is
{{#concept "bounded" Disambiguation="sequence in a preorder" Agda=is-bounded-sequence-Preorder}}
if all its values are lesser than some constant.

## Definitions

### The property of being a bounded sequence in a preorder

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2) (u : type-sequence-Preorder P)
  where

  is-upper-bound-prop-sequence-Preorder : type-Preorder P → Prop l2
  is-upper-bound-prop-sequence-Preorder K =
    Π-Prop
      ( ℕ)
      ( λ n → leq-prop-Preorder P (u n) K)

  is-upper-bound-sequence-Preorder : type-Preorder P → UU l2
  is-upper-bound-sequence-Preorder K =
    type-Prop (is-upper-bound-prop-sequence-Preorder K)

  is-bounded-prop-sequence-Preorder : Prop (l1 ⊔ l2)
  is-bounded-prop-sequence-Preorder =
    is-inhabited-subtype-Prop is-upper-bound-prop-sequence-Preorder

  is-bounded-sequence-Preorder : UU (l1 ⊔ l2)
  is-bounded-sequence-Preorder =
    type-Prop is-bounded-prop-sequence-Preorder
```

### The preorder of bounded sequences in a preorder

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  bounded-sequence-Preorder : Preorder (l1 ⊔ l2) l2
  bounded-sequence-Preorder =
    preorder-Subpreorder
      ( sequence-Preorder P)
      ( is-bounded-prop-sequence-Preorder P)

  type-bounded-sequence-Preorder : UU (l1 ⊔ l2)
  type-bounded-sequence-Preorder =
    type-Preorder (bounded-sequence-Preorder)

  seq-bounded-sequence-Preorder :
    type-bounded-sequence-Preorder →
    type-sequence-Preorder P
  seq-bounded-sequence-Preorder = pr1

  is-bounded-seq-bounded-sequence-Preorder :
    (u : type-bounded-sequence-Preorder) →
    is-bounded-sequence-Preorder
      ( P)
      ( seq-bounded-sequence-Preorder u)
  is-bounded-seq-bounded-sequence-Preorder = pr2
```

## Properties

### Constant sequences are bounded

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  is-bounded-const-sequence-Preorder :
    (x : type-Preorder P) → is-bounded-sequence-Preorder P (const ℕ x)
  is-bounded-const-sequence-Preorder x =
    unit-trunc-Prop (x , λ _ → refl-leq-Preorder P x)
```

### The type of bounded sequences in a preorder is downward closed

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  (u v : type-sequence-Preorder P)
  (I : leq-sequence-Preorder P u v)
  where

  is-upper-bound-leq-is-upper-bound-sequence-Preorder :
    (K : type-Preorder P) →
    is-upper-bound-sequence-Preorder P v K →
    is-upper-bound-sequence-Preorder P u K
  is-upper-bound-leq-is-upper-bound-sequence-Preorder K H n =
    transitive-leq-Preorder
      ( P)
      ( u n)
      ( v n)
      ( K)
      ( H n)
      ( I n)

  is-bounded-leq-is-bounded-sequence-Preorder :
    is-bounded-sequence-Preorder P v →
    is-bounded-sequence-Preorder P u
  is-bounded-leq-is-bounded-sequence-Preorder =
    map-is-inhabited (tot is-upper-bound-leq-is-upper-bound-sequence-Preorder)
```

### A sequence lesser than a bounded sequence is bounded

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  (v : type-bounded-sequence-Preorder P)
  where

  is-bounded-leq-bounded-sequence-Preorder :
    (u : type-sequence-Preorder P) →
    leq-sequence-Preorder P u (seq-bounded-sequence-Preorder P v) →
    is-bounded-sequence-Preorder P u
  is-bounded-leq-bounded-sequence-Preorder u I =
    is-bounded-leq-is-bounded-sequence-Preorder
      ( P)
      ( u)
      ( seq-bounded-sequence-Preorder P v)
      ( I)
      ( is-bounded-seq-bounded-sequence-Preorder P v)

  bounded-leq-bounded-sequence-Preorder :
    (u : type-sequence-Preorder P) →
    leq-sequence-Preorder P u (seq-bounded-sequence-Preorder P v) →
    type-bounded-sequence-Preorder P
  bounded-leq-bounded-sequence-Preorder u I =
    (u , is-bounded-leq-bounded-sequence-Preorder u I)
```

### The subtype of bounded sequences is the smallest downward closed subtype containing constant sequences

```agda
module _
  { l1 l2 l3 : Level} (P : Preorder l1 l2)
  ( Q : subtype l3 (type-sequence-Preorder P))
  ( down-Q :
    ( u v : type-sequence-Preorder P) →
    leq-sequence-Preorder P u v →
    is-in-subtype Q v →
    is-in-subtype Q u)
  ( const-Q : (x : type-Preorder P) → is-in-subtype Q (const ℕ x))
  where

  leq-subtype-downard-closed-constant-is-bounded-sequence-Preorder :
    (u : type-sequence-Preorder P) →
    is-bounded-sequence-Preorder P u →
    is-in-subtype Q u
  leq-subtype-downard-closed-constant-is-bounded-sequence-Preorder u =
    rec-trunc-Prop (Q u) (λ (x , B) → down-Q u (const ℕ x) B (const-Q x))

  leq-subtype-downard-closed-constant-seq-bounded-sequence-Preorder :
    (u : type-bounded-sequence-Preorder P) →
    is-in-subtype Q (seq-bounded-sequence-Preorder P u)
  leq-subtype-downard-closed-constant-seq-bounded-sequence-Preorder u =
    leq-subtype-downard-closed-constant-is-bounded-sequence-Preorder
      ( seq-bounded-sequence-Preorder P u)
      ( is-bounded-seq-bounded-sequence-Preorder P u)
```

### Subsequences of a bounded sequence are bounded

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  (u : type-sequence-Preorder P)
  (H : is-bounded-sequence-Preorder P u)
  where

  is-bounded-subsequence-is-bounded-sequence-Preorder :
    (v : subsequence u) →
    is-bounded-sequence-Preorder
      ( P)
      ( seq-subsequence u v)
  is-bounded-subsequence-is-bounded-sequence-Preorder v =
    map-is-inhabited
      ( tot (λ K B → B ∘ (extract-subsequence u v)))
      ( H)
```

### Bounded subsequences of a bounded sequence

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  (u : type-bounded-sequence-Preorder P)
  where

  bounded-subsequence-Preorder :
    (v : subsequence (seq-bounded-sequence-Preorder P u)) →
    type-bounded-sequence-Preorder P
  bounded-subsequence-Preorder v =
    ( seq-subsequence (seq-bounded-sequence-Preorder P u) v ,
      is-bounded-subsequence-is-bounded-sequence-Preorder
        ( P)
        ( seq-bounded-sequence-Preorder P u)
        ( is-bounded-seq-bounded-sequence-Preorder P u)
        ( v))
```
