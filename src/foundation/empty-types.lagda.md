# Empty types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.empty-types where

open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; inv-equiv; _∘e_; map-inv-equiv)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; map-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using
  ( is-prop; UU-Prop; is-trunc-is-prop; is-prop-function-type; is-prop-equiv')
open import foundation.raising-universe-levels using (raise; equiv-raise)
open import foundation.sets using (is-set; UU-Set)
open import foundation.truncated-types using
  ( is-trunc; UU-Truncated-Type)
open import foundation.truncation-levels using (𝕋; succ-𝕋)
open import foundation.universe-levels using (Level; lzero; UU)
```

## Idea

An empty type is a type with no elements. The (standard) empty type is introduced as an inductive type with no constructors. With the standard empty type available, we will say that a type is empty if it maps into the standard empty type.

## Definition

```agda
data empty : UU lzero where

ind-empty : {l : Level} {P : empty → UU l} → ((x : empty) → P x)
ind-empty ()

ex-falso : {l : Level} {A : UU l} → empty → A
ex-falso = ind-empty

is-empty : {l : Level} → UU l → UU l
is-empty A = A → empty

is-nonempty : {l : Level} → UU l → UU l
is-nonempty A = is-empty (is-empty A)
```

We raise the empty type to an arbitrary universe level

```agda
raise-empty : (l : Level) → UU l
raise-empty l = raise l empty

equiv-raise-empty : (l : Level) → empty ≃ raise-empty l
equiv-raise-empty l = equiv-raise l empty
```

## Properties

### The map `ex-falso` is an embedding

```agda
module _
  {l : Level} {A : UU l}
  where
  
  abstract
    is-emb-ex-falso : is-emb (ex-falso {A = A})
    is-emb-ex-falso ()

  ex-falso-emb : empty ↪ A
  pr1 ex-falso-emb = ex-falso
  pr2 ex-falso-emb = is-emb-ex-falso
```

### Any map into an empty type is an equivalence

```agda
abstract
  is-equiv-is-empty :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-empty B → is-equiv f
  is-equiv-is-empty f H =
    is-equiv-has-inverse
      ( ex-falso ∘ H)
      ( λ y → ex-falso (H y))
      ( λ x → ex-falso (H (f x)))

abstract
  is-equiv-is-empty' :
    {l : Level} {A : UU l} (f : is-empty A) → is-equiv f
  is-equiv-is-empty' f = is-equiv-is-empty f id

equiv-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty A → is-empty B → A ≃ B
equiv-is-empty f g =
  ( inv-equiv (pair g (is-equiv-is-empty g id))) ∘e
  ( pair f (is-equiv-is-empty f id))
```

### The empty type is a proposition

```agda
abstract
  is-prop-empty : is-prop empty
  is-prop-empty ()

empty-Prop : UU-Prop lzero
pr1 empty-Prop = empty
pr2 empty-Prop = is-prop-empty
```

### The empty type is a set

```agda
is-set-empty : is-set empty
is-set-empty ()

empty-Set : UU-Set lzero
pr1 empty-Set = empty
pr2 empty-Set = is-set-empty
```

### The empty type is k-truncated for any k ≥ 1

```agda
abstract
  is-trunc-empty : (k : 𝕋) → is-trunc (succ-𝕋 k) empty
  is-trunc-empty k ()

empty-Truncated-Type : (k : 𝕋) → UU-Truncated-Type lzero (succ-𝕋 k)
pr1 (empty-Truncated-Type k) = empty
pr2 (empty-Truncated-Type k) = is-trunc-empty k

abstract
  is-trunc-is-empty :
    {l : Level} (k : 𝕋) {A : UU l} → is-empty A → is-trunc (succ-𝕋 k) A
  is-trunc-is-empty k f = is-trunc-is-prop k (λ x → ex-falso (f x))
```

### Being empty is a proposition

```agda
is-prop-is-empty : {l : Level} {A : UU l} → is-prop (is-empty A)
is-prop-is-empty = is-prop-function-type is-prop-empty

is-empty-Prop : {l1 : Level} → UU l1 → UU-Prop l1
pr1 (is-empty-Prop A) = is-empty A
pr2 (is-empty-Prop A) = is-prop-is-empty

is-nonempty-Prop : {l1 : Level} → UU l1 → UU-Prop l1
pr1 (is-nonempty-Prop A) = is-nonempty A
pr2 (is-nonempty-Prop A) = is-prop-is-empty
```

```agda
abstract
  is-empty-type-trunc-Prop :
    {l1 : Level} {X : UU l1} → is-empty X → is-empty (type-trunc-Prop X)
  is-empty-type-trunc-Prop f =
    map-universal-property-trunc-Prop empty-Prop f

abstract
  is-empty-type-trunc-Prop' :
    {l1 : Level} {X : UU l1} → is-empty (type-trunc-Prop X) → is-empty X
  is-empty-type-trunc-Prop' f = f ∘ unit-trunc-Prop
```

### Any inhabited type is nonempty

```agda
abstract
  is-nonempty-is-inhabited :
    {l : Level} {X : UU l} → type-trunc-Prop X → is-nonempty X
  is-nonempty-is-inhabited {l} {X} =
    map-universal-property-trunc-Prop (is-nonempty-Prop X) (λ x f → f x)
```

```agda
abstract
  is-prop-raise-empty :
    {l1 : Level} → is-prop (raise-empty l1)
  is-prop-raise-empty {l1} =
    is-prop-equiv'
      ( equiv-raise l1 empty)
      ( is-prop-empty)

raise-empty-Prop :
  (l1 : Level) → UU-Prop l1
pr1 (raise-empty-Prop l1) = raise-empty l1
pr2 (raise-empty-Prop l1) = is-prop-raise-empty

abstract
  is-empty-raise-empty :
    {l1 : Level} → is-empty (raise-empty l1)
  is-empty-raise-empty {l1} = map-inv-equiv (equiv-raise-empty l1)
```
