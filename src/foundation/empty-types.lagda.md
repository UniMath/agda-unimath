# Empty types

```agda
module foundation.empty-types where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.empty-types public

open import foundation.embeddings
open import foundation.equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels

open import foundation-core.dependent-pair-types
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.sets
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.universe-levels
```

</details>

## Idea

An empty type is a type with no elements. The (standard) empty type is introduced as an inductive type with no constructors. With the standard empty type available, we will say that a type is empty if it maps into the standard empty type.

## Definition

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
is-prop-is-empty : {l : Level} {A : UU l} → is-prop (is-empty A)
is-prop-is-empty = is-prop-function-type is-prop-empty

is-empty-Prop : {l1 : Level} → UU l1 → Prop l1
pr1 (is-empty-Prop A) = is-empty A
pr2 (is-empty-Prop A) = is-prop-is-empty

is-nonempty-Prop : {l1 : Level} → UU l1 → Prop l1
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
```
