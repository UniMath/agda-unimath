# Empty types

```agda
module foundation.empty-types where

open import foundation-core.empty-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.subuniverses
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

An empty type is a type with no elements. The (standard) empty type is
introduced as an inductive type with no constructors. With the standard empty
type available, we will say that a type is empty if it maps into the standard
empty type.

## Definitions

### We raise the empty type to an arbitrary universe level

```agda
raise-empty : (l : Level) → UU l
raise-empty l = raise l empty

compute-raise-empty : (l : Level) → empty ≃ raise-empty l
compute-raise-empty l = compute-raise l empty

raise-ex-falso :
  (l1 : Level) {l2 : Level} {A : UU l2} →
  raise-empty l1 → A
raise-ex-falso l = ex-falso ∘ map-inv-equiv (compute-raise-empty l)
```

### The predicate that a subuniverse contains the empty type

```agda
contains-empty-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU l2
contains-empty-subuniverse {l1} P = is-in-subuniverse P (raise-empty l1)
```

### The predicate that a subuniverse contains any empty type

```agda
contains-empty-types-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU (lsuc l1 ⊔ l2)
contains-empty-types-subuniverse {l1} P =
  (X : UU l1) → is-empty X → is-in-subuniverse P X
```

### The predicate that a subuniverse is closed under the `is-empty` predicate

```agda
is-closed-under-is-empty-subuniverses :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (Q : subuniverse l1 l3) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
is-closed-under-is-empty-subuniverses P Q =
  (X : type-subuniverse P) →
  is-in-subuniverse Q (is-empty (inclusion-subuniverse P X))
```

## Properties

### The map `ex-falso` is an embedding

```agda
raise-ex-falso-emb :
  (l1 : Level) {l2 : Level} {A : UU l2} →
  raise-empty l1 ↪ A
raise-ex-falso-emb l =
  comp-emb ex-falso-emb (emb-equiv (inv-equiv (compute-raise-empty l)))
```

### Being empty is a proposition

```agda
is-property-is-empty : {l : Level} {A : UU l} → is-prop (is-empty A)
is-property-is-empty = is-prop-function-type is-prop-empty

is-empty-Prop : {l1 : Level} → UU l1 → Prop l1
pr1 (is-empty-Prop A) = is-empty A
pr2 (is-empty-Prop A) = is-property-is-empty

is-nonempty-Prop : {l1 : Level} → UU l1 → Prop l1
pr1 (is-nonempty-Prop A) = is-nonempty A
pr2 (is-nonempty-Prop A) = is-property-is-empty
```

### Being empty is preserved under propositional truncations

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

### Properties for the raised empty type

```agda
abstract
  is-prop-raise-empty :
    {l1 : Level} → is-prop (raise-empty l1)
  is-prop-raise-empty {l1} =
    is-prop-equiv'
      ( compute-raise l1 empty)
      ( is-prop-empty)

raise-empty-Prop :
  (l1 : Level) → Prop l1
pr1 (raise-empty-Prop l1) = raise-empty l1
pr2 (raise-empty-Prop l1) = is-prop-raise-empty

abstract
  is-empty-raise-empty :
    {l1 : Level} → is-empty (raise-empty l1)
  is-empty-raise-empty {l1} = map-inv-equiv (compute-raise-empty l1)

abstract
  is-set-raise-empty :
    {l1 : Level} → is-set (raise-empty l1)
  is-set-raise-empty = is-trunc-succ-is-trunc neg-one-𝕋 is-prop-raise-empty

raise-empty-Set :
  (l1 : Level) → Set l1
pr1 (raise-empty-Set l1) = raise-empty l1
pr2 (raise-empty-Set l1) = is-set-raise-empty
```

### The type of all empty types of a given universe is contractible

```agda
is-contr-type-is-empty :
  (l : Level) →
  is-contr (type-subuniverse is-empty-Prop)
pr1 (is-contr-type-is-empty l) = raise-empty l , is-empty-raise-empty
pr2 (is-contr-type-is-empty l) x =
  eq-pair-Σ
    ( eq-equiv
      ( equiv-is-empty
        ( is-empty-raise-empty)
        ( is-in-subuniverse-inclusion-subuniverse is-empty-Prop x)))
    ( eq-is-prop is-property-is-empty)
```

### Empty types embed into any type

```agda
abstract
  emb-is-empty :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty A → A ↪ B
  emb-is-empty H =
    ( ex-falso ∘ H ,
      is-emb-comp ex-falso H is-emb-ex-falso (is-emb-is-empty H id))
```
