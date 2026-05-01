# `1`-Types

```agda
module foundation.1-types where

open import foundation-core.1-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-truncated-types
open import foundation.subuniverse-of-truncated-types
open import foundation.subuniverses
open import foundation.truncated-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncation-levels
```

</details>

### Being a 1-type is a property

```agda
abstract
  is-prop-is-1-type :
    {l : Level} (A : UU l) → is-prop (is-1-type A)
  is-prop-is-1-type A = is-property-is-trunc one-𝕋 A

is-1-type-Prop :
  {l : Level} → UU l → Prop l
is-1-type-Prop = is-trunc-Prop one-𝕋
```

### The type of all 1-types in a universe is a 2-type

```agda
is-trunc-1-Type : {l : Level} → is-trunc two-𝕋 (1-Type l)
is-trunc-1-Type = is-trunc-Truncated-Type one-𝕋

1-Type-Truncated-Type : (l : Level) → Truncated-Type (lsuc l) two-𝕋
1-Type-Truncated-Type l = Truncated-Type-Truncated-Type l one-𝕋
```

### Products of families of 1-types are 1-types

```agda
abstract
  is-1-type-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-1-type (B x)) → is-1-type ((x : A) → B x)
  is-1-type-Π = is-trunc-Π one-𝕋

type-Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → 1-Type l2) → UU (l1 ⊔ l2)
type-Π-1-Type' A B = (x : A) → type-1-Type (B x)

is-1-type-type-Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → 1-Type l2) →
  is-1-type (type-Π-1-Type' A B)
is-1-type-type-Π-1-Type' A B =
  is-1-type-Π (λ x → is-1-type-type-1-Type (B x))

Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → 1-Type l2) → 1-Type (l1 ⊔ l2)
pr1 (Π-1-Type' A B) = type-Π-1-Type' A B
pr2 (Π-1-Type' A B) = is-1-type-type-Π-1-Type' A B

type-Π-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : type-1-Type A → 1-Type l2) →
  UU (l1 ⊔ l2)
type-Π-1-Type A = type-Π-1-Type' (type-1-Type A)

is-1-type-type-Π-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : type-1-Type A → 1-Type l2) →
  is-1-type (type-Π-1-Type A B)
is-1-type-type-Π-1-Type A = is-1-type-type-Π-1-Type' (type-1-Type A)

Π-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : type-1-Type A → 1-Type l2) →
  1-Type (l1 ⊔ l2)
Π-1-Type = Π-Truncated-Type one-𝕋
```

### The type of functions into a 1-type is a 1-type

```agda
abstract
  is-1-type-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-1-type B → is-1-type (A → B)
  is-1-type-function-type = is-trunc-function-type one-𝕋

type-hom-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : 1-Type l2) → UU (l1 ⊔ l2)
type-hom-1-Type A B = type-1-Type A → type-1-Type B

is-1-type-type-hom-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : 1-Type l2) →
  is-1-type (type-hom-1-Type A B)
is-1-type-type-hom-1-Type A B =
  is-1-type-function-type (is-1-type-type-1-Type B)

hom-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : 1-Type l2) → 1-Type (l1 ⊔ l2)
hom-1-Type = hom-Truncated-Type one-𝕋
```

### 1-Types are closed under dependent pair types

```agda
abstract
  is-1-type-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-1-type A → ((x : A) → is-1-type (B x)) → is-1-type (Σ A B)
  is-1-type-Σ = is-trunc-Σ {k = one-𝕋}

Σ-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : pr1 A → 1-Type l2) → 1-Type (l1 ⊔ l2)
Σ-1-Type = Σ-Truncated-Type
```

### 1-Types are closed under cartesian product types

```agda
abstract
  is-1-type-product :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-1-type A → is-1-type B → is-1-type (A × B)
  is-1-type-product = is-trunc-product one-𝕋

product-1-Type :
  {l1 l2 : Level} (A : 1-Type l1) (B : 1-Type l2) → 1-Type (l1 ⊔ l2)
product-1-Type A B = Σ-1-Type A (λ x → B)
```

### Subtypes of 1-types are 1-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  abstract
    is-1-type-type-subtype : is-1-type A → is-1-type (type-subtype P)
    is-1-type-type-subtype = is-trunc-type-subtype zero-𝕋 P
```

```agda
module _
  {l : Level} (X : 1-Type l)
  where

  type-equiv-1-Type : {l2 : Level} (Y : 1-Type l2) → UU (l ⊔ l2)
  type-equiv-1-Type Y = type-1-Type X ≃ type-1-Type Y

  equiv-eq-1-Type : (Y : 1-Type l) → X ＝ Y → type-equiv-1-Type Y
  equiv-eq-1-Type = equiv-eq-subuniverse is-1-type-Prop X

  abstract
    is-torsorial-equiv-1-Type :
      is-torsorial (λ (Y : 1-Type l) → type-equiv-1-Type Y)
    is-torsorial-equiv-1-Type =
      is-torsorial-equiv-subuniverse is-1-type-Prop X

  abstract
    is-equiv-equiv-eq-1-Type : (Y : 1-Type l) → is-equiv (equiv-eq-1-Type Y)
    is-equiv-equiv-eq-1-Type = is-equiv-equiv-eq-subuniverse is-1-type-Prop X

  extensionality-1-Type :
    (Y : 1-Type l) → (X ＝ Y) ≃ type-equiv-1-Type Y
  pr1 (extensionality-1-Type Y) = equiv-eq-1-Type Y
  pr2 (extensionality-1-Type Y) = is-equiv-equiv-eq-1-Type Y

  eq-equiv-1-Type : (Y : 1-Type l) → type-equiv-1-Type Y → X ＝ Y
  eq-equiv-1-Type Y = eq-equiv-subuniverse is-1-type-Prop
```

### 1-types are `k+3`-truncated for any `k`

```agda
is-trunc-is-1-type :
  {l : Level} (k : 𝕋) {A : UU l} →
  is-1-type A →
  is-trunc (succ-𝕋 (succ-𝕋 (succ-𝕋 k))) A
is-trunc-is-1-type neg-two-𝕋 is-1-type-A = is-1-type-A
is-trunc-is-1-type (succ-𝕋 k) is-1-type-A =
  is-trunc-succ-is-trunc
    ( succ-𝕋 (succ-𝕋 (succ-𝕋 k)))
    ( is-trunc-is-1-type k is-1-type-A)

1-type-Truncated-Type :
  {l : Level} (k : 𝕋) → 1-Type l → Truncated-Type l (succ-𝕋 (succ-𝕋 (succ-𝕋 k)))
pr1 (1-type-Truncated-Type k A) = type-1-Type A
pr2 (1-type-Truncated-Type k A) = is-trunc-is-1-type k (is-1-type-type-1-Type A)
```
