# Propositional truncations

```agda
module foundation.propositional-truncations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.propositions
open import foundation.truncations
open import foundation.universal-property-propositional-truncation
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-dependent-functions
open import foundation-core.sets
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

We have specified what it means to be a propositional truncation in the file
`foundation.universal-property-propositional-truncation`. Here we use the
postulate of the existence of truncations at all levels, found in the file
`foundation.truncations`, to show that propositional truncations exist.

## Definition

```agda
type-trunc-Prop : {l : Level} → UU l → UU l
type-trunc-Prop = type-trunc neg-one-𝕋

unit-trunc-Prop : {l : Level} {A : UU l} → A → type-trunc-Prop A
unit-trunc-Prop = unit-trunc

is-prop-type-trunc-Prop : {l : Level} {A : UU l} → is-prop (type-trunc-Prop A)
is-prop-type-trunc-Prop = is-trunc-type-trunc

all-elements-equal-type-trunc-Prop :
  {l : Level} {A : UU l} → all-elements-equal (type-trunc-Prop A)
all-elements-equal-type-trunc-Prop {l} {A} =
  eq-is-prop' (is-prop-type-trunc-Prop {l} {A})

trunc-Prop : {l : Level} → UU l → Prop l
trunc-Prop = trunc neg-one-𝕋
```

## Properties

### The condition in the induction principle is a property

```agda
abstract
  is-prop-condition-ind-trunc-Prop' :
    {l1 l2 : Level} {A : UU l1} {P : type-trunc-Prop A → UU l2} →
    ( (x y : type-trunc-Prop A) (u : P x) (v : P y) →
      tr P (all-elements-equal-type-trunc-Prop x y) u ＝ v) →
    (x : type-trunc-Prop A) → is-prop (P x)
  is-prop-condition-ind-trunc-Prop' {P = P} H x =
    is-prop-all-elements-equal
      ( λ u v →
        ( ap
          ( λ γ → tr P γ u)
          ( eq-is-contr (is-prop-type-trunc-Prop x x))) ∙
        ( H x x u v))
```

### The induction principle of propositional truncations

```agda
ind-trunc-Prop' :
  {l l1 : Level} {A : UU l1} (P : type-trunc-Prop A → UU l)
  (f : (x : A) → P (unit-trunc-Prop x))
  (H :
    (x y : type-trunc-Prop A) (u : P x) (v : P y) →
    tr P (all-elements-equal-type-trunc-Prop x y) u ＝ v) →
  (x : type-trunc-Prop A) → P x
ind-trunc-Prop' P f H =
  function-dependent-universal-property-trunc
    ( λ x → pair (P x) (is-prop-condition-ind-trunc-Prop' H x))
    ( f)
```

### Simplified form of the induction principle for propositional truncations

```agda
abstract
  ind-trunc-Prop :
    {l l1 : Level} {A : UU l1} (P : type-trunc-Prop A → Prop l) →
    ((x : A) → type-Prop (P (unit-trunc-Prop x))) →
    (( y : type-trunc-Prop A) → type-Prop (P y))
  ind-trunc-Prop P f =
    ind-trunc-Prop' (type-Prop ∘ P) f
      ( λ x y u v → eq-is-prop (is-prop-type-Prop (P y)))

  compute-ind-trunc-Prop :
    {l l1 : Level} {A : UU l1} (P : type-trunc-Prop A → Prop l) →
    ((precomp-Π unit-trunc-Prop (type-Prop ∘ P)) ∘ ind-trunc-Prop P) ~ id
  compute-ind-trunc-Prop P h =
    eq-is-prop (is-prop-Π (λ x → is-prop-type-Prop (P (unit-trunc-Prop x))))
```

### The defined propositional truncations are propositional truncations

```agda
abstract
  is-propositional-truncation-trunc-Prop :
    {l1 l2 : Level} (A : UU l1) →
    is-propositional-truncation l2 (trunc-Prop A) unit-trunc-Prop
  is-propositional-truncation-trunc-Prop A =
    is-propositional-truncation-extension-property
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( λ {l} Q → ind-trunc-Prop (λ x → Q))
```

### The defined propositional truncations satisfy the universal property of propositional truncations

```agda
abstract
  universal-property-trunc-Prop :
    {l1 l2 : Level} (A : UU l1) →
    universal-property-propositional-truncation l2
      ( trunc-Prop A)
      ( unit-trunc-Prop)
  universal-property-trunc-Prop A =
    universal-property-is-propositional-truncation _
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( is-propositional-truncation-trunc-Prop A)

abstract
  map-universal-property-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (P : Prop l2) →
    (A → type-Prop P) → type-hom-Prop (trunc-Prop A) P
  map-universal-property-trunc-Prop {A = A} P f =
    map-is-propositional-truncation
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( is-propositional-truncation-trunc-Prop A)
      ( P)
      ( f)

abstract
  apply-universal-property-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (t : type-trunc-Prop A) (P : Prop l2) →
    (A → type-Prop P) → type-Prop P
  apply-universal-property-trunc-Prop t P f =
    map-universal-property-trunc-Prop P f t

abstract
  apply-twice-universal-property-trunc-Prop :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (u : type-trunc-Prop A)
    (v : type-trunc-Prop B) (P : Prop l3) →
    (A → B → type-Prop P) → type-Prop P
  apply-twice-universal-property-trunc-Prop u v P f =
    apply-universal-property-trunc-Prop u P
      ( λ x → apply-universal-property-trunc-Prop v P (f x))

abstract
  apply-three-times-universal-property-trunc-Prop :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
    (u : type-trunc-Prop A) (v : type-trunc-Prop B) (w : type-trunc-Prop C) →
    (P : Prop l4) → (A → B → C → type-Prop P) → type-Prop P
  apply-three-times-universal-property-trunc-Prop u v w P f =
    apply-universal-property-trunc-Prop u P
      ( λ x → apply-twice-universal-property-trunc-Prop v w P (f x))
```

### The propositional truncation of a type is `k+1`-truncated

```agda
is-trunc-trunc-Prop :
  {l : Level} (k : 𝕋) {A : UU l} → is-trunc (succ-𝕋 k) (type-trunc-Prop A)
is-trunc-trunc-Prop k = is-trunc-is-prop k is-prop-type-trunc-Prop

truncated-type-trunc-Prop :
  {l : Level} (k : 𝕋) → UU l → Truncated-Type l (succ-𝕋 k)
pr1 (truncated-type-trunc-Prop k A) = type-trunc-Prop A
pr2 (truncated-type-trunc-Prop k A) = is-trunc-trunc-Prop k

set-trunc-Prop : {l : Level} → UU l → Set l
set-trunc-Prop = truncated-type-trunc-Prop neg-one-𝕋
```

### A proposition is equivalent to its propositional truncation

```agda
module _
  {l : Level} (A : Prop l)
  where

  equiv-unit-trunc-Prop : type-Prop A ≃ type-trunc-Prop (type-Prop A)
  equiv-unit-trunc-Prop = equiv-unit-trunc A
```

### The propositional truncation is idempotent

```agda
module _
  {l : Level} (A : UU l)
  where

  abstract
    map-idempotent-trunc-Prop :
      type-trunc-Prop (type-trunc-Prop A) → type-trunc-Prop A
    map-idempotent-trunc-Prop =
      map-universal-property-trunc-Prop (trunc-Prop A) id

  abstract
    is-equiv-map-idempotent-trunc-Prop : is-equiv map-idempotent-trunc-Prop
    is-equiv-map-idempotent-trunc-Prop =
      is-equiv-is-prop
        ( is-prop-type-trunc-Prop)
        ( is-prop-type-trunc-Prop)
        ( unit-trunc-Prop)

  idempotent-trunc-Prop :
    type-trunc-Prop (type-trunc-Prop A) ≃ type-trunc-Prop A
  pr1 idempotent-trunc-Prop = map-idempotent-trunc-Prop
  pr2 idempotent-trunc-Prop = is-equiv-map-idempotent-trunc-Prop

  abstract
    is-equiv-map-inv-idempotent-trunc-Prop :
      is-equiv (unit-trunc-Prop {A = type-trunc-Prop A})
    is-equiv-map-inv-idempotent-trunc-Prop =
      is-equiv-is-prop
        ( is-prop-type-trunc-Prop)
        ( is-prop-type-trunc-Prop)
        ( map-idempotent-trunc-Prop)

  inv-idempotent-trunc-Prop :
    type-trunc-Prop A ≃ type-trunc-Prop (type-trunc-Prop A)
  pr1 inv-idempotent-trunc-Prop = unit-trunc-Prop
  pr2 inv-idempotent-trunc-Prop = is-equiv-map-inv-idempotent-trunc-Prop
```

### Propositional truncations satisfy the dependent universal property of the propositional truncation

```agda
abstract
  dependent-universal-property-trunc-Prop :
    {l1 : Level} {A : UU l1} {l : Level} →
      dependent-universal-property-propositional-truncation l
      ( trunc-Prop A)
      ( unit-trunc-Prop)
  dependent-universal-property-trunc-Prop {A = A} =
    dependent-universal-property-is-propositional-truncation
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( is-propositional-truncation-trunc-Prop A)

module _
  {l1 l2 : Level} {A : UU l1} (P : type-trunc-Prop A → Prop l2)
  where

  equiv-dependent-universal-property-trunc-Prop :
    ((y : type-trunc-Prop A) → type-Prop (P y)) ≃
    ((x : A) → type-Prop (P (unit-trunc-Prop x)))
  pr1 equiv-dependent-universal-property-trunc-Prop =
    precomp-Π unit-trunc-Prop (type-Prop ∘ P)
  pr2 equiv-dependent-universal-property-trunc-Prop =
    dependent-universal-property-trunc-Prop P

  apply-dependent-universal-property-trunc-Prop :
    (y : type-trunc-Prop A) → ((x : A) → type-Prop (P (unit-trunc-Prop x))) →
    type-Prop (P y)
  apply-dependent-universal-property-trunc-Prop y f =
    map-inv-equiv equiv-dependent-universal-property-trunc-Prop f y
```

### Propositional truncations distribute over cartesian products

```agda
equiv-prod-trunc-Prop :
  {l1 l2 : Level} (A : UU l1) (A' : UU l2) →
  type-equiv-Prop
    ( trunc-Prop (A × A'))
    ( prod-Prop (trunc-Prop A) (trunc-Prop A'))
equiv-prod-trunc-Prop A A' =
  pr1
    ( center
      ( is-uniquely-unique-propositional-truncation
        ( trunc-Prop (A × A'))
        ( prod-Prop (trunc-Prop A) (trunc-Prop A'))
        ( unit-trunc-Prop)
        ( map-prod unit-trunc-Prop unit-trunc-Prop)
        ( is-propositional-truncation-trunc-Prop (A × A'))
        ( is-propositional-truncation-prod
          ( trunc-Prop A)
          ( unit-trunc-Prop)
          ( trunc-Prop A')
          ( unit-trunc-Prop)
          ( is-propositional-truncation-trunc-Prop A)
          ( is-propositional-truncation-trunc-Prop A'))))

map-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop (A × B) → type-trunc-Prop A × type-trunc-Prop B
map-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
  map-universal-property-trunc-Prop
    ( pair
      ( type-trunc-Prop A × type-trunc-Prop B)
      ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop))
    ( map-prod unit-trunc-Prop unit-trunc-Prop)

map-inv-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop A × type-trunc-Prop B → type-trunc-Prop (A × B)
map-inv-distributive-trunc-prod-Prop {l1} {l2} {A} {B} t =
  map-universal-property-trunc-Prop
    ( trunc-Prop (A × B))
    ( λ x →
      map-universal-property-trunc-Prop
        ( trunc-Prop (A × B))
        ( unit-trunc-Prop ∘ (pair x))
        ( pr2 t))
    ( pr1 t)

abstract
  is-equiv-map-distributive-trunc-prod-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-equiv (map-distributive-trunc-prod-Prop {A = A} {B = B})
  is-equiv-map-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
    is-equiv-is-prop
      ( is-prop-type-trunc-Prop)
      ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
      ( map-inv-distributive-trunc-prod-Prop)

distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop (A × B) ≃ (type-trunc-Prop A × type-trunc-Prop B)
pr1 distributive-trunc-prod-Prop = map-distributive-trunc-prod-Prop
pr2 distributive-trunc-prod-Prop = is-equiv-map-distributive-trunc-prod-Prop

abstract
  is-equiv-map-inv-distributive-trunc-prod-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-equiv (map-inv-distributive-trunc-prod-Prop {A = A} {B = B})
  is-equiv-map-inv-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
    is-equiv-is-prop
      ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
      ( is-prop-type-trunc-Prop)
      ( map-distributive-trunc-prod-Prop)

inv-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ( type-trunc-Prop A × type-trunc-Prop B) ≃ type-trunc-Prop (A × B)
pr1 inv-distributive-trunc-prod-Prop = map-inv-distributive-trunc-prod-Prop
pr2 inv-distributive-trunc-prod-Prop =
  is-equiv-map-inv-distributive-trunc-prod-Prop
```

### Propositional truncations of coproducts of types with themselves

```agda
module _
  {l : Level} {A : UU l} where
  map-trunc-Prop-diagonal-coprod : type-trunc-Prop (A + A) → type-trunc-Prop A
  map-trunc-Prop-diagonal-coprod =
    map-universal-property-trunc-Prop
      ( trunc-Prop A)
      ( unit-trunc ∘
        ind-coprod (λ _ → A) id id)

  map-inv-trunc-Prop-diagonal-coprod :
    type-trunc-Prop A → type-trunc-Prop (A + A)
  map-inv-trunc-Prop-diagonal-coprod =
    map-universal-property-trunc-Prop
      ( trunc-Prop (A + A))
      ( unit-trunc ∘ (inl ∘ id))

  abstract
    is-equiv-map-trunc-Prop-diagonal-coprod :
      is-equiv map-trunc-Prop-diagonal-coprod
    is-equiv-map-trunc-Prop-diagonal-coprod =
      is-equiv-is-prop
        is-prop-type-trunc-Prop
        is-prop-type-trunc-Prop
        map-inv-trunc-Prop-diagonal-coprod

    is-equiv-map-inv-trunc-Prop-diagonal-coprod :
      is-equiv map-inv-trunc-Prop-diagonal-coprod
    is-equiv-map-inv-trunc-Prop-diagonal-coprod =
      is-equiv-is-prop
        is-prop-type-trunc-Prop
        is-prop-type-trunc-Prop
        map-trunc-Prop-diagonal-coprod

  equiv-trunc-Prop-diagonal-coprod :
    (type-trunc-Prop (A + A)) ≃ type-trunc-Prop A
  pr1 equiv-trunc-Prop-diagonal-coprod = map-trunc-Prop-diagonal-coprod
  pr2 equiv-trunc-Prop-diagonal-coprod = is-equiv-map-trunc-Prop-diagonal-coprod

  inv-equiv-trunc-Prop-diagonal-coprod :
    (type-trunc-Prop A) ≃ type-trunc-Prop (A + A)
  pr1 inv-equiv-trunc-Prop-diagonal-coprod = map-inv-trunc-Prop-diagonal-coprod
  pr2 inv-equiv-trunc-Prop-diagonal-coprod =
    is-equiv-map-inv-trunc-Prop-diagonal-coprod
```
