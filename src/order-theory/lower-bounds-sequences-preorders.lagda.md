# Lower bounds of sequences in preorders

```agda
module order-theory.lower-bounds-sequences-preorders where
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
{{#concept "bounded-below" Disambiguation="sequence in a preorder" Agda=is-bounded-below-sequence-Preorder}}
if all its values are greater than some constant.

## Definitions

### The property of being a lower bound of a sequence in a preorder

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2) (u : type-sequence-Preorder P)
  where

  is-lower-bound-prop-sequence-Preorder : type-Preorder P → Prop l2
  is-lower-bound-prop-sequence-Preorder K =
    Π-Prop
      ( ℕ)
      ( λ n → leq-prop-Preorder P K (u n))

  is-lower-bound-sequence-Preorder : type-Preorder P → UU l2
  is-lower-bound-sequence-Preorder K =
    type-Prop (is-lower-bound-prop-sequence-Preorder K)

  is-bounded-below-prop-sequence-Preorder : Prop (l1 ⊔ l2)
  is-bounded-below-prop-sequence-Preorder =
    is-inhabited-subtype-Prop is-lower-bound-prop-sequence-Preorder

  is-bounded-below-sequence-Preorder : UU (l1 ⊔ l2)
  is-bounded-below-sequence-Preorder =
    type-Prop is-bounded-below-prop-sequence-Preorder
```

### The preorder of bounded-below sequences in a preorder

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  bounded-below-sequence-Preorder : Preorder (l1 ⊔ l2) l2
  bounded-below-sequence-Preorder =
    preorder-Subpreorder
      ( sequence-Preorder P)
      ( is-bounded-below-prop-sequence-Preorder P)

  type-bounded-below-sequence-Preorder : UU (l1 ⊔ l2)
  type-bounded-below-sequence-Preorder =
    type-Preorder (bounded-below-sequence-Preorder)

  seq-bounded-below-sequence-Preorder :
    type-bounded-below-sequence-Preorder →
    type-sequence-Preorder P
  seq-bounded-below-sequence-Preorder = pr1

  is-bounded-below-seq-bounded-below-sequence-Preorder :
    (u : type-bounded-below-sequence-Preorder) →
    is-bounded-below-sequence-Preorder
      ( P)
      ( seq-bounded-below-sequence-Preorder u)
  is-bounded-below-seq-bounded-below-sequence-Preorder = pr2
```

## Properties

### Constant sequences are bounded below

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  is-bounded-below-const-sequence-Preorder :
    (x : type-Preorder P) → is-bounded-below-sequence-Preorder P (const ℕ x)
  is-bounded-below-const-sequence-Preorder x =
    unit-trunc-Prop (x , λ _ → refl-leq-Preorder P x)
```

### The type of bounded-below sequences in a preorder is upward closed

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  (u v : type-sequence-Preorder P)
  (I : leq-sequence-Preorder P u v)
  where

  is-lower-bound-leq-is-lower-bound-sequence-Preorder :
    (K : type-Preorder P) →
    is-lower-bound-sequence-Preorder P u K →
    is-lower-bound-sequence-Preorder P v K
  is-lower-bound-leq-is-lower-bound-sequence-Preorder K H n =
    transitive-leq-Preorder
      ( P)
      ( K)
      ( u n)
      ( v n)
      ( I n)
      ( H n)

  is-bounded-below-leq-is-bounded-below-sequence-Preorder :
    is-bounded-below-sequence-Preorder P u →
    is-bounded-below-sequence-Preorder P v
  is-bounded-below-leq-is-bounded-below-sequence-Preorder =
    map-is-inhabited (tot is-lower-bound-leq-is-lower-bound-sequence-Preorder)
```

### The subtype of bounded-below sequences is the smallest upward closed subtype containing constant sequences

```agda
module _
  { l1 l2 l3 : Level} (P : Preorder l1 l2)
  ( Q : subtype l3 (type-sequence-Preorder P))
  ( up-Q :
    ( u v : type-sequence-Preorder P) →
    leq-sequence-Preorder P u v →
    is-in-subtype Q u →
    is-in-subtype Q v)
  ( const-Q : (x : type-Preorder P) → is-in-subtype Q (const ℕ x))
  where

  leq-subtype-upward-closed-constant-is-bounded-below-sequence-Preorder :
    (u : type-sequence-Preorder P) →
    is-bounded-below-sequence-Preorder P u →
    is-in-subtype Q u
  leq-subtype-upward-closed-constant-is-bounded-below-sequence-Preorder u =
    rec-trunc-Prop (Q u) (λ (x , B) → up-Q (const ℕ x) u B (const-Q x))

  leq-subtype-upward-closed-constant-seq-bounded-below-sequence-Preorder :
    (u : type-bounded-below-sequence-Preorder P) →
    is-in-subtype Q (seq-bounded-below-sequence-Preorder P u)
  leq-subtype-upward-closed-constant-seq-bounded-below-sequence-Preorder u =
    leq-subtype-upward-closed-constant-is-bounded-below-sequence-Preorder
      ( seq-bounded-below-sequence-Preorder P u)
      ( is-bounded-below-seq-bounded-below-sequence-Preorder P u)
```

### A sequence bounded below by a sequence with a lower bound is bounded below

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  is-bounded-below-leq-bounded-below-sequence-Preorder :
    (u : type-bounded-below-sequence-Preorder P) →
    (v : type-sequence-Preorder P) →
    leq-sequence-Preorder P (seq-bounded-below-sequence-Preorder P u) v →
    is-bounded-below-sequence-Preorder P v
  is-bounded-below-leq-bounded-below-sequence-Preorder u v I =
    is-bounded-below-leq-is-bounded-below-sequence-Preorder
      ( P)
      ( seq-bounded-below-sequence-Preorder P u)
      ( v)
      ( I)
      ( is-bounded-below-seq-bounded-below-sequence-Preorder P u)

  bounded-below-leq-bounded-below-sequence-Preorder :
    (u : type-bounded-below-sequence-Preorder P) →
    (v : type-sequence-Preorder P) →
    leq-sequence-Preorder P (seq-bounded-below-sequence-Preorder P u) v →
    type-bounded-below-sequence-Preorder P
  bounded-below-leq-bounded-below-sequence-Preorder u v I =
    (v , is-bounded-below-leq-bounded-below-sequence-Preorder u v I)
```

### A lower bound of a sequence bounds all its subsequences

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  (u : type-sequence-Preorder P)
  (H : is-bounded-below-sequence-Preorder P u)
  where

  is-bounded-below-subsequence-is-bounded-below-sequence-Preorder :
    (v : subsequence u) →
    is-bounded-below-sequence-Preorder
      ( P)
      ( seq-subsequence u v)
  is-bounded-below-subsequence-is-bounded-below-sequence-Preorder v =
    map-is-inhabited
      ( tot (λ K B → B ∘ (extract-subsequence u v)))
      ( H)
```

### Bounded-below subsequences of a bounded-below sequence

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  (u : type-bounded-below-sequence-Preorder P)
  where

  bounded-below-subsequence-Preorder :
    (v : subsequence (seq-bounded-below-sequence-Preorder P u)) →
    type-bounded-below-sequence-Preorder P
  bounded-below-subsequence-Preorder v =
    ( seq-subsequence (seq-bounded-below-sequence-Preorder P u) v ,
      is-bounded-below-subsequence-is-bounded-below-sequence-Preorder
        ( P)
        ( seq-bounded-below-sequence-Preorder P u)
        ( is-bounded-below-seq-bounded-below-sequence-Preorder P u)
        ( v))
```
