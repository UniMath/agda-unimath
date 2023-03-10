# Locally small types

```agda
module foundation.locally-small-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.propositions
open import foundation.subtypes
open import foundation.subuniverses
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.small-types
```

</details>

## Idea

A type is said to be locally small if its identity types are small.

## Definition

```agda
is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-locally-small l A = (x y : A) → is-small l (x ＝ y)
```

### The type of locally small types

```agda
Locally-Small-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Locally-Small-Type l1 l2 = Σ (UU l2) (is-locally-small l1)

module _
  {l1 l2 : Level} (A : Locally-Small-Type l1 l2)
  where

  type-Locally-Small-Type : UU l2
  type-Locally-Small-Type = pr1 A

  is-locally-small-type-Locally-Small-Type :
    is-locally-small l1 type-Locally-Small-Type
  is-locally-small-type-Locally-Small-Type = pr2 A
```

## Properties

### Being locally small is a property

```agda
is-prop-is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-locally-small l A)
is-prop-is-locally-small l A =
  is-prop-Π (λ x → is-prop-Π (λ y → is-prop-is-small l (x ＝ y)))

is-locally-small-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → Prop (lsuc l ⊔ l1)
pr1 (is-locally-small-Prop l A) = is-locally-small l A
pr2 (is-locally-small-Prop l A) = is-prop-is-locally-small l A
```

### Any small type is locally small

```agda
is-locally-small-is-small :
  {l l1 : Level} {A : UU l1} → is-small l A → is-locally-small l A
pr1 (is-locally-small-is-small (pair X e) x y) =
  map-equiv e x ＝ map-equiv e y
pr2 (is-locally-small-is-small (pair X e) x y) = equiv-ap e x y
```

### Any proposition is locally small

```agda
is-locally-small-is-prop :
  (l : Level) {l1 : Level} {A : UU l1} → is-prop A → is-locally-small l A
is-locally-small-is-prop l H x y = is-small-is-contr l (H x y)
```

### Any univalent universe is locally small

```agda
is-locally-small-UU :
  {l : Level} → is-locally-small l (UU l)
pr1 (is-locally-small-UU X Y) = X ≃ Y
pr2 (is-locally-small-UU X Y) = equiv-univalence
```

### Any Σ-type of locally small types is locally small

```agda
is-locally-small-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  is-locally-small l3 A → ((x : A) → is-locally-small l4 (B x)) →
  is-locally-small (l3 ⊔ l4) (Σ A B)
is-locally-small-Σ H K x y =
  is-small-equiv
    ( Eq-Σ x y)
    ( equiv-pair-eq-Σ x y)
    ( is-small-Σ
      ( H (pr1 x) (pr1 y))
      ( λ p → K (pr1 y) (tr _ p (pr2 x)) (pr2 y)))

Σ-Locally-Small-Type :
  {l1 l2 l3 l4 : Level} (A : Locally-Small-Type l1 l2) →
  (type-Locally-Small-Type A → Locally-Small-Type l3 l4) →
  Locally-Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (Σ-Locally-Small-Type A B) =
  Σ (type-Locally-Small-Type A) (λ a → type-Locally-Small-Type (B a))
pr2 (Σ-Locally-Small-Type A B) =
  is-locally-small-Σ
    ( is-locally-small-type-Locally-Small-Type A)
    ( λ a → is-locally-small-type-Locally-Small-Type (B a))
```

### The underlying type of a subtype of a locally small type is locally small

```agda
is-locally-small-type-subtype :
  {l1 l2 l3 : Level} {A : UU l1} (P : subtype l2 A) →
  is-locally-small l3 A → is-locally-small l3 (type-subtype P)
is-locally-small-type-subtype {l3 = l3} P H =
  is-locally-small-Σ H
    (λ a → is-locally-small-is-prop l3 (is-prop-is-in-subtype P a))

type-subtype-Locally-Small-Type :
  {l1 l2 l3 : Level} (A : Locally-Small-Type l1 l2) →
  subtype l3 (type-Locally-Small-Type A) → Locally-Small-Type l1 (l2 ⊔ l3)
pr1 (type-subtype-Locally-Small-Type A P) = type-subtype P
pr2 (type-subtype-Locally-Small-Type A P) =
  is-locally-small-type-subtype P (is-locally-small-type-Locally-Small-Type A)
```

### Any product of locally small types indexed by a small type is small

```agda
is-locally-small-Π :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  is-small l3 A → ((x : A) → is-locally-small l4 (B x)) →
  is-locally-small (l3 ⊔ l4) ((x : A) → B x)
is-locally-small-Π {l1} {l2} {l3} {l4} H K f g =
  is-small-equiv
    ( f ~ g)
    ( equiv-funext)
    ( is-small-Π H (λ x → K x (f x) (g x)))

Π-Locally-Small-Type :
  {l1 l2 l3 l4 : Level} (A : Small-Type l1 l2) →
  (type-Small-Type A → Locally-Small-Type l3 l4) →
  Locally-Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (Π-Locally-Small-Type A B) =
  (a : type-Small-Type A) → type-Locally-Small-Type (B a)
pr2 (Π-Locally-Small-Type A B) =
  is-locally-small-Π
    ( is-small-type-Small-Type A)
    ( λ a → is-locally-small-type-Locally-Small-Type (B a))
```

### The type of types in any given subuniverse is locally small

```agda
is-locally-small-type-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  is-locally-small l1 (type-subuniverse P)
is-locally-small-type-subuniverse P =
  is-locally-small-type-subtype P is-locally-small-UU
```

### The type of locally small types is locally small

```agda
is-locally-small-Locally-Small-Type :
  {l1 l2 : Level} → is-locally-small l2 (Locally-Small-Type l1 l2)
is-locally-small-Locally-Small-Type {l1} {l2} =
  is-locally-small-type-subuniverse ( is-locally-small-Prop l1)
```

### The type of truncated types is locally small

```agda
is-locally-small-Truncated-Type :
  {l : Level} (k : 𝕋) → is-locally-small l (Truncated-Type l k)
is-locally-small-Truncated-Type k =
  is-locally-small-type-subuniverse (is-trunc-Prop k)
```

### The type of propositions is locally small

```agda
is-locally-small-type-Prop :
  {l : Level} → is-locally-small l (Prop l)
is-locally-small-type-Prop = is-locally-small-Truncated-Type neg-one-𝕋
```

### The type of subtypes of a small type is locally small

```agda
is-locally-small-subtype :
  {l1 l2 l3 : Level} {A : UU l1} →
  is-small l2 A → is-locally-small (l2 ⊔ l3) (subtype l3 A)
is-locally-small-subtype H =
  is-locally-small-Π H (λ a → is-locally-small-type-Prop)
```

### The type of inhabited subtypes of a small type is locally small

```agda
is-locally-small-inhabited-subtype :
  {l1 l2 l3 : Level} {A : UU l1} →
  is-small l2 A → is-locally-small (l2 ⊔ l3) (inhabited-subtype l3 A)
is-locally-small-inhabited-subtype H =
  is-locally-small-type-subtype
    ( is-inhabited-subtype-Prop)
    ( is-locally-small-subtype H)
```
