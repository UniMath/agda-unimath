# De Morgan subtypes

```agda
module logic.de-morgan-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositional-maps
open import foundation.sets
open import foundation.structured-type-duality
open import foundation.subtypes
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import logic.de-morgan-embeddings
open import logic.de-morgan-maps
open import logic.de-morgan-propositions
open import logic.de-morgan-types
```

</details>

## Idea

A
{{#concept "De Morgan subtype" Disambiguation="of a type" Agda=is-de-morgan-subtype Agda=de-morgan-subtype}}
of a type consists of a family of
[De Morgan propositions](logic.de-morgan-propositions.md) over it.

## Definitions

### De Morgan subtypes

```agda
is-de-morgan-subtype-Prop :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → Prop (l1 ⊔ l2)
is-de-morgan-subtype-Prop {A = A} P =
  Π-Prop A (λ a → is-de-morgan-Prop (type-Prop (P a)))

is-de-morgan-subtype :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → UU (l1 ⊔ l2)
is-de-morgan-subtype P =
  type-Prop (is-de-morgan-subtype-Prop P)

is-prop-is-de-morgan-subtype :
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) →
  is-prop (is-de-morgan-subtype P)
is-prop-is-de-morgan-subtype P =
  is-prop-type-Prop (is-de-morgan-subtype-Prop P)

de-morgan-subtype :
  {l1 : Level} (l : Level) (X : UU l1) → UU (l1 ⊔ lsuc l)
de-morgan-subtype l X = X → De-Morgan-Prop l
```

### The underlying subtype of a De Morgan subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : de-morgan-subtype l2 A)
  where

  subtype-de-morgan-subtype : subtype l2 A
  subtype-de-morgan-subtype a =
    prop-De-Morgan-Prop (P a)

  is-de-morgan-de-morgan-subtype :
    is-de-morgan-subtype subtype-de-morgan-subtype
  is-de-morgan-de-morgan-subtype a =
    is-de-morgan-type-De-Morgan-Prop (P a)

  is-in-de-morgan-subtype : A → UU l2
  is-in-de-morgan-subtype =
    is-in-subtype subtype-de-morgan-subtype

  is-prop-is-in-de-morgan-subtype :
    (a : A) → is-prop (is-in-de-morgan-subtype a)
  is-prop-is-in-de-morgan-subtype =
    is-prop-is-in-subtype subtype-de-morgan-subtype
```

### The underlying type of a De Morgan subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : de-morgan-subtype l2 A)
  where

  type-de-morgan-subtype : UU (l1 ⊔ l2)
  type-de-morgan-subtype =
    type-subtype (subtype-de-morgan-subtype P)

  inclusion-de-morgan-subtype :
    type-de-morgan-subtype → A
  inclusion-de-morgan-subtype =
    inclusion-subtype (subtype-de-morgan-subtype P)

  is-emb-inclusion-de-morgan-subtype :
    is-emb inclusion-de-morgan-subtype
  is-emb-inclusion-de-morgan-subtype =
    is-emb-inclusion-subtype (subtype-de-morgan-subtype P)

  is-de-morgan-map-inclusion-de-morgan-subtype :
    is-de-morgan-map inclusion-de-morgan-subtype
  is-de-morgan-map-inclusion-de-morgan-subtype x =
    is-de-morgan-equiv
      ( equiv-fiber-pr1 (type-De-Morgan-Prop ∘ P) x)
      ( is-de-morgan-type-De-Morgan-Prop (P x))

  is-injective-inclusion-de-morgan-subtype :
    is-injective inclusion-de-morgan-subtype
  is-injective-inclusion-de-morgan-subtype =
    is-injective-inclusion-subtype (subtype-de-morgan-subtype P)

  emb-de-morgan-subtype : type-de-morgan-subtype ↪ A
  emb-de-morgan-subtype =
    emb-subtype (subtype-de-morgan-subtype P)

  is-de-morgan-emb-inclusion-de-morgan-subtype :
    is-de-morgan-emb inclusion-de-morgan-subtype
  is-de-morgan-emb-inclusion-de-morgan-subtype =
    ( is-emb-inclusion-de-morgan-subtype ,
      is-de-morgan-map-inclusion-de-morgan-subtype)

  de-morgan-emb-de-morgan-subtype :
    type-de-morgan-subtype ↪ᵈᵐ A
  de-morgan-emb-de-morgan-subtype =
    ( inclusion-de-morgan-subtype ,
      is-de-morgan-emb-inclusion-de-morgan-subtype)
```

### The De Morgan subtype associated to a De Morgan embedding

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ᵈᵐ Y)
  where

  de-morgan-subtype-de-morgan-emb :
    de-morgan-subtype (l1 ⊔ l2) Y
  pr1 (de-morgan-subtype-de-morgan-emb y) =
    fiber (map-de-morgan-emb f) y
  pr2 (de-morgan-subtype-de-morgan-emb y) =
    is-de-morgan-prop-map-is-de-morgan-emb
      ( is-de-morgan-emb-map-de-morgan-emb f)
      ( y)

  compute-type-de-morgan-type-de-morgan-emb :
    type-de-morgan-subtype
      de-morgan-subtype-de-morgan-emb ≃
    X
  compute-type-de-morgan-type-de-morgan-emb =
    equiv-total-fiber (map-de-morgan-emb f)

  inv-compute-type-de-morgan-type-de-morgan-emb :
    X ≃
    type-de-morgan-subtype
      de-morgan-subtype-de-morgan-emb
  inv-compute-type-de-morgan-type-de-morgan-emb =
    inv-equiv-total-fiber (map-de-morgan-emb f)
```

## Examples

### The De Morgan subtypes of left and right elements in a coproduct type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-de-morgan-is-left :
    (x : A + B) → is-de-morgan (is-left x)
  is-de-morgan-is-left (inl x) = is-de-morgan-unit
  is-de-morgan-is-left (inr x) = is-de-morgan-empty

  is-left-De-Morgan-Prop :
    A + B → De-Morgan-Prop lzero
  pr1 (is-left-De-Morgan-Prop x) = is-left x
  pr1 (pr2 (is-left-De-Morgan-Prop x)) = is-prop-is-left x
  pr2 (pr2 (is-left-De-Morgan-Prop x)) =
    is-de-morgan-is-left x

  is-de-morgan-is-right :
    (x : A + B) → is-de-morgan (is-right x)
  is-de-morgan-is-right (inl x) = is-de-morgan-empty
  is-de-morgan-is-right (inr x) = is-de-morgan-unit

  is-right-De-Morgan-Prop :
    A + B → De-Morgan-Prop lzero
  pr1 (is-right-De-Morgan-Prop x) = is-right x
  pr1 (pr2 (is-right-De-Morgan-Prop x)) = is-prop-is-right x
  pr2 (pr2 (is-right-De-Morgan-Prop x)) =
    is-de-morgan-is-right x
```

## Properties

### A De Morgan subtype of a `k+1`-truncated type is `k+1`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} (P : de-morgan-subtype l2 A)
  where

  abstract
    is-trunc-type-de-morgan-subtype :
      is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k)
      (type-de-morgan-subtype P)
    is-trunc-type-de-morgan-subtype =
      is-trunc-type-subtype k (subtype-de-morgan-subtype P)

module _
  {l1 l2 : Level} {A : UU l1} (P : de-morgan-subtype l2 A)
  where

  abstract
    is-prop-type-de-morgan-subtype :
      is-prop A → is-prop (type-de-morgan-subtype P)
    is-prop-type-de-morgan-subtype =
      is-prop-type-subtype (subtype-de-morgan-subtype P)

  abstract
    is-set-type-de-morgan-subtype :
      is-set A → is-set (type-de-morgan-subtype P)
    is-set-type-de-morgan-subtype =
      is-set-type-subtype (subtype-de-morgan-subtype P)

  abstract
    is-1-type-type-de-morgan-subtype :
      is-1-type A → is-1-type (type-de-morgan-subtype P)
    is-1-type-type-de-morgan-subtype =
      is-1-type-type-subtype (subtype-de-morgan-subtype P)

prop-de-morgan-subprop :
  {l1 l2 : Level} (A : Prop l1)
  (P : de-morgan-subtype l2 (type-Prop A)) →
  Prop (l1 ⊔ l2)
prop-de-morgan-subprop A P =
  prop-subprop A (subtype-de-morgan-subtype P)

set-de-morgan-subset :
  {l1 l2 : Level} (A : Set l1)
  (P : de-morgan-subtype l2 (type-Set A)) →
  Set (l1 ⊔ l2)
set-de-morgan-subset A P =
  set-subset A (subtype-de-morgan-subtype P)
```

### The type of De Morgan subtypes of a type is a set

```agda
is-set-de-morgan-subtype :
  {l1 l2 : Level} {X : UU l1} → is-set (de-morgan-subtype l2 X)
is-set-de-morgan-subtype =
  is-set-function-type is-set-De-Morgan-Prop
```

### Extensionality of the type of De Morgan subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : de-morgan-subtype l2 A)
  where

  has-same-elements-de-morgan-subtype :
    {l3 : Level} → de-morgan-subtype l3 A → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-de-morgan-subtype Q =
    has-same-elements-subtype
      ( subtype-de-morgan-subtype P)
      ( subtype-de-morgan-subtype Q)

  extensionality-de-morgan-subtype :
    (Q : de-morgan-subtype l2 A) →
    (P ＝ Q) ≃ has-same-elements-de-morgan-subtype Q
  extensionality-de-morgan-subtype =
    extensionality-Π P
      ( λ x Q →
        ( type-De-Morgan-Prop (P x)) ↔
        ( type-De-Morgan-Prop Q))
      ( λ x Q → extensionality-De-Morgan-Prop (P x) Q)

  has-same-elements-eq-de-morgan-subtype :
    (Q : de-morgan-subtype l2 A) →
    (P ＝ Q) → has-same-elements-de-morgan-subtype Q
  has-same-elements-eq-de-morgan-subtype Q =
    map-equiv (extensionality-de-morgan-subtype Q)

  eq-has-same-elements-de-morgan-subtype :
    (Q : de-morgan-subtype l2 A) →
    has-same-elements-de-morgan-subtype Q → P ＝ Q
  eq-has-same-elements-de-morgan-subtype Q =
    map-inv-equiv (extensionality-de-morgan-subtype Q)

  refl-extensionality-de-morgan-subtype :
    map-equiv (extensionality-de-morgan-subtype P) refl ＝
    (λ x → id , id)
  refl-extensionality-de-morgan-subtype = refl
```

### The type of De Morgan subtypes of `A` is equivalent to the type of all De Morgan embeddings into a type `A`

```agda
equiv-Fiber-De-Morgan-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Σ (UU (l1 ⊔ l)) (λ X → X ↪ᵈᵐ A) ≃ (de-morgan-subtype (l1 ⊔ l) A)
equiv-Fiber-De-Morgan-Prop l A =
  ( equiv-Fiber-structure l is-de-morgan-prop A) ∘e
  ( equiv-tot
    ( λ X →
      equiv-tot
        ( λ f →
          ( inv-distributive-Π-Σ) ∘e
          ( equiv-product-left (equiv-is-prop-map-is-emb f)))))
```
