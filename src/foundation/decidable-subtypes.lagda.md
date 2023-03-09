# Decidable subtypes

```agda
module foundation.decidable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels
```

</details>

## Idea

A decidable subtype of a type consists of a family of decidable propositions over it.

## Definitions

### Decidable subtypes

```agda
is-decidable-subtype-Prop :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → Prop (l1 ⊔ l2)
is-decidable-subtype-Prop {A = A} P =
  Π-Prop A (λ a → is-decidable-Prop (P a))

is-decidable-subtype : {l1 l2 : Level} {A : UU l1} → subtype l2 A → UU (l1 ⊔ l2)
is-decidable-subtype P = type-Prop (is-decidable-subtype-Prop P)

is-prop-is-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) →
  is-prop (is-decidable-subtype P)
is-prop-is-decidable-subtype P = is-prop-type-Prop (is-decidable-subtype-Prop P)

decidable-subtype : {l1 : Level} (l : Level) (X : UU l1) → UU (l1 ⊔ lsuc l)
decidable-subtype l X = X → decidable-Prop l
```

### The underlying subtype of a decidable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  subtype-decidable-subtype : subtype l2 A
  subtype-decidable-subtype a = prop-decidable-Prop (P a)

  is-decidable-subtype-decidable-subtype :
    is-decidable-subtype subtype-decidable-subtype
  is-decidable-subtype-decidable-subtype a =
    is-decidable-type-decidable-Prop (P a)

  is-in-decidable-subtype : A → UU l2
  is-in-decidable-subtype = is-in-subtype subtype-decidable-subtype

  is-prop-is-in-decidable-subtype :
    (a : A) → is-prop (is-in-decidable-subtype a)
  is-prop-is-in-decidable-subtype =
    is-prop-is-in-subtype subtype-decidable-subtype
```

### The underlying type of a decidable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  type-decidable-subtype : UU (l1 ⊔ l2)
  type-decidable-subtype = type-subtype (subtype-decidable-subtype P)

  inclusion-decidable-subtype : type-decidable-subtype → A
  inclusion-decidable-subtype = inclusion-subtype (subtype-decidable-subtype P)

  is-emb-inclusion-decidable-subtype : is-emb inclusion-decidable-subtype
  is-emb-inclusion-decidable-subtype =
    is-emb-inclusion-subtype (subtype-decidable-subtype P)

  is-injective-inclusion-decidable-subtype :
    is-injective inclusion-decidable-subtype
  is-injective-inclusion-decidable-subtype =
    is-injective-inclusion-subtype (subtype-decidable-subtype P)

  emb-decidable-subtype : type-decidable-subtype ↪ A
  emb-decidable-subtype = emb-subtype (subtype-decidable-subtype P)
```

## Examples

### The decidable subtypes of left and right elements in a coproduct type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-is-left : (x : A + B) → is-decidable (is-left x)
  is-decidable-is-left (inl x) = is-decidable-unit
  is-decidable-is-left (inr x) = is-decidable-empty

  is-left-decidable-Prop : A + B → decidable-Prop lzero
  pr1 (is-left-decidable-Prop x) = is-left x
  pr1 (pr2 (is-left-decidable-Prop x)) = is-prop-is-left x
  pr2 (pr2 (is-left-decidable-Prop x)) = is-decidable-is-left x

  is-decidable-is-right : (x : A + B) → is-decidable (is-right x)
  is-decidable-is-right (inl x) = is-decidable-empty
  is-decidable-is-right (inr x) = is-decidable-unit

  is-right-decidable-Prop : A + B → decidable-Prop lzero
  pr1 (is-right-decidable-Prop x) = is-right x
  pr1 (pr2 (is-right-decidable-Prop x)) = is-prop-is-right x
  pr2 (pr2 (is-right-decidable-Prop x)) = is-decidable-is-right x
```

## Properties

### Types of decidable subtypes of any universe level are equivalent

```agda
module _
  {l1 : Level} (X : UU l1)
  where

  equiv-universes-decidable-subtype : (l l' : Level) →
    decidable-subtype l X ≃ decidable-subtype l' X
  equiv-universes-decidable-subtype l l' =
    equiv-Π
      ( λ _ → decidable-Prop l')
      ( id-equiv)
      ( λ _ → equiv-universes-decidable-Prop l l')

  iff-universes-decidable-subtype : (l l' : Level) (S : decidable-subtype l X) →
    ( (x : X) →
      prop-decidable-Prop (S x) ⇔
      prop-decidable-Prop (map-equiv (equiv-universes-decidable-subtype l l') S x))
  iff-universes-decidable-subtype l l' S x =
    tr
      ( λ P → prop-decidable-Prop (S x) ⇔ prop-decidable-Prop P)
      ( inv
        ( compute-map-equiv-Π
          ( λ _ → decidable-Prop l')
          ( id-equiv)
          ( λ _ → equiv-universes-decidable-Prop l l')
          ( S)
          ( x)))
      ( iff-universes-decidable-Prop l l' (S x))
```

### A decidable subtype of a (k+1)-truncated type is (k+1)-truncated.

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} (P : decidable-subtype l2 A)
  where

  abstract
    is-trunc-type-decidable-subtype :
      is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (type-decidable-subtype P)
    is-trunc-type-decidable-subtype =
      is-trunc-type-subtype k (subtype-decidable-subtype P)

module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  abstract
    is-prop-type-decidable-subtype :
      is-prop A → is-prop (type-decidable-subtype P)
    is-prop-type-decidable-subtype =
      is-prop-type-subtype (subtype-decidable-subtype P)

  abstract
    is-set-type-decidable-subtype : is-set A → is-set (type-decidable-subtype P)
    is-set-type-decidable-subtype =
      is-set-type-subtype (subtype-decidable-subtype P)

  abstract
    is-1-type-type-decidable-subtype :
      is-1-type A → is-1-type (type-decidable-subtype P)
    is-1-type-type-decidable-subtype =
      is-1-type-type-subtype (subtype-decidable-subtype P)

prop-decidable-subprop :
  {l1 l2 : Level} (A : Prop l1) (P : decidable-subtype l2 (type-Prop A)) →
  Prop (l1 ⊔ l2)
prop-decidable-subprop A P = prop-subprop A (subtype-decidable-subtype P)

set-decidable-subset :
  {l1 l2 : Level} (A : Set l1) (P : decidable-subtype l2 (type-Set A)) →
  Set (l1 ⊔ l2)
set-decidable-subset A P = set-subset A (subtype-decidable-subtype P)
```

### The type of decidable subtypes of a type is a set

```agda
is-set-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} → is-set (decidable-subtype l2 X)
is-set-decidable-subtype {l1} {l2} {X} =
  is-set-function-type is-set-decidable-Prop
```

### Extensionality of the type of decidable subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  has-same-elements-decidable-subtype :
    {l3 : Level} → decidable-subtype l3 A → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-decidable-subtype Q =
    has-same-elements-subtype
      ( subtype-decidable-subtype P)
      ( subtype-decidable-subtype Q)

  extensionality-decidable-subtype :
    (Q : decidable-subtype l2 A) →
    (P ＝ Q) ≃ has-same-elements-decidable-subtype Q
  extensionality-decidable-subtype =
    extensionality-Π P
      ( λ x Q → prop-decidable-Prop (P x) ⇔ prop-decidable-Prop Q)
      ( λ x Q → extensionality-decidable-Prop (P x) Q)

  has-same-elements-eq-decidable-subtype :
    (Q : decidable-subtype l2 A) →
    (P ＝ Q) → has-same-elements-decidable-subtype Q
  has-same-elements-eq-decidable-subtype Q =
    map-equiv (extensionality-decidable-subtype Q)

  eq-has-same-elements-decidable-subtype :
    (Q : decidable-subtype l2 A) →
    has-same-elements-decidable-subtype Q → P ＝ Q
  eq-has-same-elements-decidable-subtype Q =
    map-inv-equiv (extensionality-decidable-subtype Q)

  refl-extensionality-decidable-subtype :
    map-equiv (extensionality-decidable-subtype P) refl ＝ (λ x → pair id id)
  refl-extensionality-decidable-subtype = refl
```
