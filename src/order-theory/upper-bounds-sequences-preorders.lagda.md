# Upper bounds of sequences in preorders

```agda
module order-theory.upper-bounds-sequences-preorders where
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
{{#concept "bounded-above" Disambiguation="sequence in a preorder" Agda=is-bounded-above-sequence-Preorder}}
if all its values are lesser than some constant.

## Definitions

### The property of being an upper bound of a sequence in a preorder

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

  is-bounded-above-prop-sequence-Preorder : Prop (l1 ⊔ l2)
  is-bounded-above-prop-sequence-Preorder =
    is-inhabited-subtype-Prop is-upper-bound-prop-sequence-Preorder

  is-bounded-above-sequence-Preorder : UU (l1 ⊔ l2)
  is-bounded-above-sequence-Preorder =
    type-Prop is-bounded-above-prop-sequence-Preorder
```

### The preorder of bounded-above sequences in a preorder

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  bounded-above-sequence-Preorder : Preorder (l1 ⊔ l2) l2
  bounded-above-sequence-Preorder =
    preorder-Subpreorder
      ( sequence-Preorder P)
      ( is-bounded-above-prop-sequence-Preorder P)

  type-bounded-above-sequence-Preorder : UU (l1 ⊔ l2)
  type-bounded-above-sequence-Preorder =
    type-Preorder (bounded-above-sequence-Preorder)

  seq-bounded-above-sequence-Preorder :
    type-bounded-above-sequence-Preorder →
    type-sequence-Preorder P
  seq-bounded-above-sequence-Preorder = pr1

  is-bounded-above-seq-bounded-above-sequence-Preorder :
    (u : type-bounded-above-sequence-Preorder) →
    is-bounded-above-sequence-Preorder
      ( P)
      ( seq-bounded-above-sequence-Preorder u)
  is-bounded-above-seq-bounded-above-sequence-Preorder = pr2
```

## Properties

### Constant sequences are bounded above

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  is-bounded-above-const-sequence-Preorder :
    (x : type-Preorder P) → is-bounded-above-sequence-Preorder P (const ℕ x)
  is-bounded-above-const-sequence-Preorder x =
    unit-trunc-Prop (x , λ _ → refl-leq-Preorder P x)
```

### The type of bounded-above sequences in a preorder is downward closed

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

  is-bounded-above-leq-is-bounded-above-sequence-Preorder :
    is-bounded-above-sequence-Preorder P v →
    is-bounded-above-sequence-Preorder P u
  is-bounded-above-leq-is-bounded-above-sequence-Preorder =
    map-is-inhabited (tot is-upper-bound-leq-is-upper-bound-sequence-Preorder)
```

### The subtype of bounded-above sequences is the smallest downward closed subtype containing constant sequences

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

  leq-subtype-downward-closed-constant-is-bounded-above-sequence-Preorder :
    (u : type-sequence-Preorder P) →
    is-bounded-above-sequence-Preorder P u →
    is-in-subtype Q u
  leq-subtype-downward-closed-constant-is-bounded-above-sequence-Preorder u =
    rec-trunc-Prop (Q u) (λ (x , B) → down-Q u (const ℕ x) B (const-Q x))

  leq-subtype-downward-closed-constant-seq-bounded-above-sequence-Preorder :
    (u : type-bounded-above-sequence-Preorder P) →
    is-in-subtype Q (seq-bounded-above-sequence-Preorder P u)
  leq-subtype-downward-closed-constant-seq-bounded-above-sequence-Preorder u =
    leq-subtype-downward-closed-constant-is-bounded-above-sequence-Preorder
      ( seq-bounded-above-sequence-Preorder P u)
      ( is-bounded-above-seq-bounded-above-sequence-Preorder P u)
```

### A sequence bounded above by a sequence with an upper bound is bounded above

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  is-bounded-above-leq-bounded-above-sequence-Preorder :
    (u : type-sequence-Preorder P) →
    (v : type-bounded-above-sequence-Preorder P) →
    leq-sequence-Preorder P u (seq-bounded-above-sequence-Preorder P v) →
    is-bounded-above-sequence-Preorder P u
  is-bounded-above-leq-bounded-above-sequence-Preorder u v I =
    is-bounded-above-leq-is-bounded-above-sequence-Preorder
      ( P)
      ( u)
      ( seq-bounded-above-sequence-Preorder P v)
      ( I)
      ( is-bounded-above-seq-bounded-above-sequence-Preorder P v)

  bounded-above-leq-bounded-above-sequence-Preorder :
    (u : type-sequence-Preorder P) →
    (v : type-bounded-above-sequence-Preorder P) →
    leq-sequence-Preorder P u (seq-bounded-above-sequence-Preorder P v) →
    type-bounded-above-sequence-Preorder P
  bounded-above-leq-bounded-above-sequence-Preorder u v I =
    (u , is-bounded-above-leq-bounded-above-sequence-Preorder u v I)
```

### An upper bound of a sequence bounds all its subsequences

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  (u : type-sequence-Preorder P)
  (H : is-bounded-above-sequence-Preorder P u)
  where

  is-bounded-above-subsequence-is-bounded-above-sequence-Preorder :
    (v : subsequence u) →
    is-bounded-above-sequence-Preorder
      ( P)
      ( seq-subsequence u v)
  is-bounded-above-subsequence-is-bounded-above-sequence-Preorder v =
    map-is-inhabited
      ( tot (λ K B → B ∘ (extract-subsequence u v)))
      ( H)
```

### Bounded-above subsequences of a bounded-above sequence

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  (u : type-bounded-above-sequence-Preorder P)
  where

  bounded-above-subsequence-Preorder :
    (v : subsequence (seq-bounded-above-sequence-Preorder P u)) →
    type-bounded-above-sequence-Preorder P
  bounded-above-subsequence-Preorder v =
    ( seq-subsequence (seq-bounded-above-sequence-Preorder P u) v ,
      is-bounded-above-subsequence-is-bounded-above-sequence-Preorder
        ( P)
        ( seq-bounded-above-sequence-Preorder P u)
        ( is-bounded-above-seq-bounded-above-sequence-Preorder P u)
        ( v))
```
