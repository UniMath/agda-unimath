# Mere identity systems

```agda
module foundation.mere-identity-systems where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.binary-relations
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-systems
open import foundation-core.identity-types
open import foundation.logical-equivalences
open import foundation-core.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

There are two kinds of mere identity systems: unary and binary mere identity systems.

### Unary mere identity systems

A [subtype](foundation.subtypes.md) `P : A → Prop` containing an element `a : A` is said to be a unary {{#concept "mere identity system" Disambiguation="unary"}} if for every `Q : (x : A) → P x → Prop` the evaluation map at the witness `ρ : P a`

```text
  ((x : A) (p : P x) → Q x p) → Q a ρ
```

is an [equivalence](foundation-core.equivalences.md). The following conditions are equivalent to being a unary mere identity system

1. The underlying type of `P` is [`0`-connected](foundation.0-connected-types.md).
2. The subtype `P` contains the same elements as the subtype of all elements [merely equal](foundation.mere-equality.md) to `a`.
3. The evaluation map

   ```text
     ((x : A) → P x → Q x) → Q a
   ```

   is an equivalence for every subtype `Q : A → Prop`. In this case we say that `P` is the {{#concept "least subtype containing a given element"}} `a`.

### Binary mere identity systems

A reflexive [binary relation](foundation.binary-relations.md) `R : A → A → Prop` valued in [foundation-core.propositions.md) is said to be a binary {{#concept "mere identity system" Disambiguation="binary"}} if for every `S : (x y : A) → R x y → Prop` the evaluation map at the reflexivity element `ρ`

```text
  ((x y : A) (r : R x y) → S x y r) → S a a (ρ a)
```

is an [equivalence](foundation-core.equivalences.md) for every element `a : A`. The following conditions are equivalent to being a binary mere identity system

1. The [total space](foundation.dependent-pair-types.md) `Σ A (R a)` is [`0`-connected](foundation.0-connected-types.md) for every element `a : A`.
2. The relation `R` relates the same elements as the [mere equality relation](foundation.mere-equality.md).
3. The evaluation map

   ```text
     ((x y : A) → R x y → S x y) → S a a
   ```

   is an equivalence for every binary relation `S : A → A → Prop`.
4. The subtype `R a : A → Prop` is a unary mere identitity system for every `a : A`.

## Definitions

### The predicate of being a unary mere identity system

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) {a : A} (ρ : is-in-subtype P a)
  where

  ev-element-subtype :
    {l : Level} (Q : (x : A) → is-in-subtype P x → Prop l) →
    ((x : A) (p : is-in-subtype P x) → is-in-subtype (Q x) p) →
    is-in-subtype (Q a) ρ
  ev-element-subtype Q f = f a ρ

  is-mere-identity-system-subtype : UUω
  is-mere-identity-system-subtype =
    {l : Level} (Q : (x : A) → is-in-subtype P x → Prop l) →
    is-equiv (ev-element-subtype Q)

  ind-mere-identity-system-subtype :
    is-mere-identity-system-subtype →
    {l : Level} (Q : (x : A) → is-in-subtype P x → Prop l) →
    type-Prop (Q a ρ) → (x : A) (p : is-in-subtype P x) → type-Prop (Q x p)
  ind-mere-identity-system-subtype H Q =
    map-inv-is-equiv (H Q)

  rec-mere-identity-system-subtype :
    is-mere-identity-system-subtype →
    {l : Level} (Q : subtype l A) →
    is-in-subtype Q a → (x : A) → is-in-subtype P x → is-in-subtype Q x
  rec-mere-identity-system-subtype H Q =
    ind-mere-identity-system-subtype H (λ x _ → Q x)
```

### The predicate of being a `0`-connected subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  is-0-connected-prop-subtype : Prop (l1 ⊔ l2)
  is-0-connected-prop-subtype = is-0-connected-Prop (type-subtype P)

  is-0-connected-subtype : UU (l1 ⊔ l2)
  is-0-connected-subtype = type-Prop is-0-connected-prop-subtype

  is-prop-is-0-connected-subtype : is-prop is-0-connected-subtype
  is-prop-is-0-connected-subtype = is-prop-type-Prop is-0-connected-prop-subtype
```

### The predicate of being the least subtype containing an element

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) {a : A} (ρ : is-in-subtype P a)
  where

  is-least-subtype-containing-element : UUω
  is-least-subtype-containing-element =
    {l : Level} (Q : subtype l A) →
    is-equiv (ev-element-subtype P ρ (λ x _ → Q x))
```

### The predicate of being a binary mere identity system

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  (ρ : is-reflexive-Relation-Prop R)
  where

  ev-refl-Reflexive-Relation-Prop :
    {l : Level} (S : (x y : A) → subtype l (type-Relation-Prop R x y)) →
    ((x y : A) (r : type-Relation-Prop R x y) → is-in-subtype (S x y) r) →
    (x : A) → is-in-subtype (S x x) (ρ x)
  ev-refl-Reflexive-Relation-Prop S f x = f x x (ρ x)

  is-mere-identity-system-Reflexive-Relation-Prop : UUω
  is-mere-identity-system-Reflexive-Relation-Prop =
    {l : Level} (S : (x y : A) → subtype l (type-Relation-Prop R x y)) →
    is-equiv (ev-refl-Reflexive-Relation-Prop S)
```

### The predicate of being the least reflexive relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  (ρ : is-reflexive-Relation-Prop R)
  where

  is-least-Reflexive-Relation-Prop : UUω
  is-least-Reflexive-Relation-Prop =
    {l : Level} (S : Relation-Prop l A) →
    is-equiv (ev-refl-Reflexive-Relation-Prop R ρ (λ x y _ → S x y))
```

## Properties

### Any unary identity system is a `0`-connected subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) {a : A} (ρ : is-in-subtype P a)
  where

  is-0-connected-is-mere-identity-system-subtype :
    is-mere-identity-system-subtype P ρ → is-0-connected-subtype P
  is-0-connected-is-mere-identity-system-subtype H =
    is-0-connected-dependent-universal-property-0-connected-type
      ( a , ρ)
      ( λ Q → is-equiv-comp _ _ is-equiv-ev-pair (H (λ x y → Q (x , y))))
```

### The extension of a unary mere identity system to the set truncation is an identity system

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) {a : A} (ρ : is-in-subtype P a)
  (H : is-mere-identity-system-subtype P ρ)
  where

  abstract
    is-torsorial-extension-trunc-set-subtype-is-mere-identity-system :
      is-torsorial (is-in-extension-trunc-set-subtype P)
    is-torsorial-extension-trunc-set-subtype-is-mere-identity-system =
      is-contr-equiv'
        ( type-trunc-Set (type-subtype P))
        ( compute-type-extension-trunc-set-subtype P)
        ( is-0-connected-is-mere-identity-system-subtype P ρ H)

  abstract
    is-identity-system-extension-trunc-set-subtype-is-mere-identity-system :
      is-identity-system
        ( is-in-extension-trunc-set-subtype P)
        ( unit-trunc-Set a)
        ( is-in-extension-trunc-set-is-in-subtype P a ρ)
    is-identity-system-extension-trunc-set-subtype-is-mere-identity-system =
      is-identity-system-is-torsorial
        ( unit-trunc-Set a)
        ( is-in-extension-trunc-set-is-in-subtype P a ρ)
        ( is-torsorial-extension-trunc-set-subtype-is-mere-identity-system)
```

### Mere equality is a mere identity system

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  abstract
    is-mere-identity-system-mere-eq :
      is-mere-identity-system-subtype (mere-eq-Prop a) (refl-mere-eq a)
    is-mere-identity-system-mere-eq P =
      is-equiv-has-converse-is-prop
        ( is-prop-Π (λ x → is-prop-Π (is-prop-is-in-subtype (P x))))
        ( is-prop-is-in-subtype (P a) (refl-mere-eq a))
        ( λ p x → ind-trunc-Prop (P x) (λ where refl → p))

  abstract
    ind-mere-identity-system-mere-eq :
      {l : Level} (P : (x : A) → mere-eq a x → Prop l) →
      (p : type-Prop (P a (refl-mere-eq a))) →
      (x : A) (r : mere-eq a x) → type-Prop (P x r)
    ind-mere-identity-system-mere-eq =
      ind-mere-identity-system-subtype
        ( mere-eq-Prop a)
        ( refl-mere-eq a)
        ( is-mere-identity-system-mere-eq)

  abstract
    rec-mere-identity-system-mere-eq :
      {l : Level} (P : subtype l A) →
      (p : is-in-subtype P a) (x : A) (r : mere-eq a x) → is-in-subtype P x
    rec-mere-identity-system-mere-eq =
      rec-mere-identity-system-subtype
        ( mere-eq-Prop a)
        ( refl-mere-eq a)
        ( is-mere-identity-system-mere-eq)
```

### Any unary mere identity system has the same elements as the subtype of elements merely equal to the base point

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) {a : A} (ρ : is-in-subtype P a)
  (H : is-mere-identity-system-subtype P ρ)
  where

  has-same-elements-mere-eq-is-mere-identity-system-subtype :
    has-same-elements-subtype (mere-eq-Prop a) P
  pr1 (has-same-elements-mere-eq-is-mere-identity-system-subtype x) =
    rec-mere-identity-system-mere-eq a P ρ x
  pr2 (has-same-elements-mere-eq-is-mere-identity-system-subtype x) =
    rec-mere-identity-system-subtype P ρ H (mere-eq-Prop a) (refl-mere-eq a) x
```
