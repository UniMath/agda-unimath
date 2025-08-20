# Propositional truncations

```agda
module foundation.propositional-truncations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.constant-type-families
open import foundation.dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.truncations
open import foundation.universal-property-propositional-truncation
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.dependent-identifications
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.precomposition-dependent-functions
open import foundation-core.precomposition-functions
open import foundation-core.sections
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

║_║₋₁ : {l : Level} → UU l → UU l
║_║₋₁ = type-trunc-Prop

unit-trunc-Prop : {l : Level} {A : UU l} → A → ║ A ║₋₁
unit-trunc-Prop = unit-trunc

is-prop-type-trunc-Prop : {l : Level} {A : UU l} → is-prop (║ A ║₋₁)
is-prop-type-trunc-Prop = is-trunc-type-trunc

all-elements-equal-type-trunc-Prop :
  {l : Level} {A : UU l} → all-elements-equal (║ A ║₋₁)
all-elements-equal-type-trunc-Prop {l} {A} =
  eq-is-prop' (is-prop-type-trunc-Prop {l} {A})

trunc-Prop : {l : Level} → UU l → Prop l
trunc-Prop = trunc neg-one-𝕋
```

**Notation.** The [box drawings double vertical](https://codepoints.net/U+2551)
symbol `║` in the propositional truncation notation `║_║₋₁` can be inserted with
`agda-input` using the escape sequence `\--=` and selecting the second item in
the list.

## Properties

### The condition in the induction principle is a property

```agda
abstract
  is-prop-condition-ind-trunc-Prop' :
    {l1 l2 : Level} {A : UU l1} {P : ║ A ║₋₁ → UU l2} →
    ( (x y : ║ A ║₋₁) (u : P x) (v : P y) →
      dependent-identification P (all-elements-equal-type-trunc-Prop x y) u v) →
    (x : ║ A ║₋₁) → is-prop (P x)
  is-prop-condition-ind-trunc-Prop' {P = P} H x =
    is-prop-all-elements-equal
      ( λ u v →
        ( ap
          ( λ γ → tr P γ u)
          ( eq-is-contr (is-prop-type-trunc-Prop x x))) ∙
        ( H x x u v))
```

### The induction principle for propositional truncations

```agda
ind-trunc-Prop' :
  {l l1 : Level} {A : UU l1} (P : ║ A ║₋₁ → UU l)
  (f : (x : A) → P (unit-trunc-Prop x))
  (H :
    (x y : ║ A ║₋₁) (u : P x) (v : P y) →
    dependent-identification P (all-elements-equal-type-trunc-Prop x y) u v) →
  (x : ║ A ║₋₁) → P x
ind-trunc-Prop' P f H =
  function-dependent-universal-property-trunc
    ( λ x → (P x , is-prop-condition-ind-trunc-Prop' H x))
    ( f)
```

### The recursion principle for propositional truncations

```agda
rec-trunc-Prop' :
  {l l1 : Level} {A : UU l1} {P : UU l}
  (f : A → P) (H : ║ A ║₋₁ → (u v : P) → u ＝ v) →
  ║ A ║₋₁ → P
rec-trunc-Prop' {P = P} f H =
  ind-trunc-Prop'
    ( λ _ → P)
    ( f)
    ( λ x y u v →
      map-compute-dependent-identification-constant-type-family
        ( all-elements-equal-type-trunc-Prop x y)
        ( H x u v))
```

### The propositional induction principle for propositional truncations

```agda
module _
  {l l1 : Level} {A : UU l1} (P : ║ A ║₋₁ → Prop l)
  where

  abstract
    ind-trunc-Prop :
      ((x : A) → type-Prop (P (unit-trunc-Prop x))) →
      (( y : ║ A ║₋₁) → type-Prop (P y))
    ind-trunc-Prop f =
      ind-trunc-Prop' (type-Prop ∘ P) f
        ( λ x y u v → eq-is-prop (is-prop-type-Prop (P y)))

    compute-ind-trunc-Prop :
        is-section (precomp-Π unit-trunc-Prop (type-Prop ∘ P)) (ind-trunc-Prop)
    compute-ind-trunc-Prop h =
      eq-is-prop (is-prop-Π (λ x → is-prop-type-Prop (P (unit-trunc-Prop x))))
```

### The propositional recursion principle for propositional truncations

```agda
module _
  {l l1 : Level} {A : UU l1} (P : Prop l)
  where

  abstract
    rec-trunc-Prop :
      (A → type-Prop P) → (║ A ║₋₁ → type-Prop P)
    rec-trunc-Prop = ind-trunc-Prop (λ _ → P)

    compute-rec-trunc-Prop :
      is-section (precomp unit-trunc-Prop (type-Prop P)) (rec-trunc-Prop)
    compute-rec-trunc-Prop = compute-ind-trunc-Prop (λ _ → P)
```

### The defined propositional truncations are propositional truncations

```agda
abstract
  is-propositional-truncation-trunc-Prop :
    {l : Level} (A : UU l) →
    is-propositional-truncation (trunc-Prop A) unit-trunc-Prop
  is-propositional-truncation-trunc-Prop A =
    is-propositional-truncation-extension-property
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( λ Q → ind-trunc-Prop (λ x → Q))
```

### The defined propositional truncations satisfy the universal property of propositional truncations

```agda
abstract
  universal-property-trunc-Prop :
    {l : Level} (A : UU l) →
    universal-property-propositional-truncation
      ( trunc-Prop A)
      ( unit-trunc-Prop)
  universal-property-trunc-Prop A =
    universal-property-is-propositional-truncation
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
    {l1 l2 : Level} {A : UU l1} (t : ║ A ║₋₁) (P : Prop l2) →
    (A → type-Prop P) → type-Prop P
  apply-universal-property-trunc-Prop t P f =
    map-universal-property-trunc-Prop P f t

abstract
  apply-twice-universal-property-trunc-Prop :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (u : ║ A ║₋₁)
    (v : ║ B ║₋₁) (P : Prop l3) →
    (A → B → type-Prop P) → type-Prop P
  apply-twice-universal-property-trunc-Prop u v P f =
    apply-universal-property-trunc-Prop u P
      ( λ x → apply-universal-property-trunc-Prop v P (f x))

abstract
  apply-three-times-universal-property-trunc-Prop :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
    (u : ║ A ║₋₁) (v : ║ B ║₋₁) (w : ║ C ║₋₁) →
    (P : Prop l4) → (A → B → C → type-Prop P) → type-Prop P
  apply-three-times-universal-property-trunc-Prop u v w P f =
    apply-universal-property-trunc-Prop u P
      ( λ x → apply-twice-universal-property-trunc-Prop v w P (f x))
```

### The propositional truncation of a type is `k+1`-truncated

```agda
is-trunc-trunc-Prop :
  {l : Level} (k : 𝕋) {A : UU l} → is-trunc (succ-𝕋 k) (║ A ║₋₁)
is-trunc-trunc-Prop k = is-trunc-is-prop k is-prop-type-trunc-Prop

truncated-type-trunc-Prop :
  {l : Level} (k : 𝕋) → UU l → Truncated-Type l (succ-𝕋 k)
pr1 (truncated-type-trunc-Prop k A) = ║ A ║₋₁
pr2 (truncated-type-trunc-Prop k A) = is-trunc-trunc-Prop k

set-trunc-Prop : {l : Level} → UU l → Set l
set-trunc-Prop = truncated-type-trunc-Prop neg-one-𝕋
```

### A proposition is equivalent to its propositional truncation

```agda
module _
  {l : Level} (A : Prop l)
  where

  equiv-unit-trunc-Prop : type-Prop A ≃ ║ type-Prop A ║₋₁
  equiv-unit-trunc-Prop = equiv-unit-trunc A
```

### The propositional truncation is idempotent

```agda
module _
  {l : Level} (A : UU l)
  where

  abstract
    map-idempotent-trunc-Prop :
      ║ (║ A ║₋₁) ║₋₁ → ║ A ║₋₁
    map-idempotent-trunc-Prop =
      map-universal-property-trunc-Prop (trunc-Prop A) id

  abstract
    is-equiv-map-idempotent-trunc-Prop : is-equiv map-idempotent-trunc-Prop
    is-equiv-map-idempotent-trunc-Prop =
      is-equiv-has-converse-is-prop
        ( is-prop-type-trunc-Prop)
        ( is-prop-type-trunc-Prop)
        ( unit-trunc-Prop)

  idempotent-trunc-Prop :
    ║ (║ A ║₋₁) ║₋₁ ≃ ║ A ║₋₁
  pr1 idempotent-trunc-Prop = map-idempotent-trunc-Prop
  pr2 idempotent-trunc-Prop = is-equiv-map-idempotent-trunc-Prop

  abstract
    is-equiv-map-inv-idempotent-trunc-Prop :
      is-equiv (unit-trunc-Prop {A = ║ A ║₋₁})
    is-equiv-map-inv-idempotent-trunc-Prop =
      is-equiv-has-converse-is-prop
        ( is-prop-type-trunc-Prop)
        ( is-prop-type-trunc-Prop)
        ( map-idempotent-trunc-Prop)

  inv-idempotent-trunc-Prop :
    ║ A ║₋₁ ≃ ║ (║ A ║₋₁) ║₋₁
  pr1 inv-idempotent-trunc-Prop = unit-trunc-Prop
  pr2 inv-idempotent-trunc-Prop = is-equiv-map-inv-idempotent-trunc-Prop
```

### Propositional truncations satisfy the dependent universal property of the propositional truncation

```agda
abstract
  dependent-universal-property-trunc-Prop :
    {l : Level} {A : UU l} →
    dependent-universal-property-propositional-truncation
      ( trunc-Prop A)
      ( unit-trunc-Prop)
  dependent-universal-property-trunc-Prop {A = A} =
    dependent-universal-property-is-propositional-truncation
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( is-propositional-truncation-trunc-Prop A)

module _
  {l1 l2 : Level} {A : UU l1} (P : ║ A ║₋₁ → Prop l2)
  where

  equiv-dependent-universal-property-trunc-Prop :
    ((y : ║ A ║₋₁) → type-Prop (P y)) ≃
    ((x : A) → type-Prop (P (unit-trunc-Prop x)))
  pr1 equiv-dependent-universal-property-trunc-Prop =
    precomp-Π unit-trunc-Prop (type-Prop ∘ P)
  pr2 equiv-dependent-universal-property-trunc-Prop =
    dependent-universal-property-trunc-Prop P

  apply-dependent-universal-property-trunc-Prop :
    (y : ║ A ║₋₁) → ((x : A) → type-Prop (P (unit-trunc-Prop x))) →
    type-Prop (P y)
  apply-dependent-universal-property-trunc-Prop y f =
    map-inv-equiv equiv-dependent-universal-property-trunc-Prop f y
```

### Propositional truncations distribute over cartesian products

```agda
equiv-product-trunc-Prop :
  {l1 l2 : Level} (A : UU l1) (A' : UU l2) →
  type-equiv-Prop
    ( trunc-Prop (A × A'))
    ( product-Prop (trunc-Prop A) (trunc-Prop A'))
equiv-product-trunc-Prop A A' =
  pr1
    ( center
      ( is-uniquely-unique-propositional-truncation
        ( trunc-Prop (A × A'))
        ( product-Prop (trunc-Prop A) (trunc-Prop A'))
        ( unit-trunc-Prop)
        ( map-product unit-trunc-Prop unit-trunc-Prop)
        ( is-propositional-truncation-trunc-Prop (A × A'))
        ( is-propositional-truncation-product
          ( trunc-Prop A)
          ( unit-trunc-Prop)
          ( trunc-Prop A')
          ( unit-trunc-Prop)
          ( is-propositional-truncation-trunc-Prop A)
          ( is-propositional-truncation-trunc-Prop A'))))

map-distributive-trunc-product-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ║ A × B ║₋₁ → ║ A ║₋₁ × ║ B ║₋₁
map-distributive-trunc-product-Prop {l1} {l2} {A} {B} =
  map-universal-property-trunc-Prop
    ( pair
      ( ║ A ║₋₁ × ║ B ║₋₁)
      ( is-prop-product is-prop-type-trunc-Prop is-prop-type-trunc-Prop))
    ( map-product unit-trunc-Prop unit-trunc-Prop)

map-inv-distributive-trunc-product-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ║ A ║₋₁ × ║ B ║₋₁ → ║ A × B ║₋₁
map-inv-distributive-trunc-product-Prop {l1} {l2} {A} {B} t =
  map-universal-property-trunc-Prop
    ( trunc-Prop (A × B))
    ( λ x →
      map-universal-property-trunc-Prop
        ( trunc-Prop (A × B))
        ( unit-trunc-Prop ∘ (pair x))
        ( pr2 t))
    ( pr1 t)

abstract
  is-equiv-map-distributive-trunc-product-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-equiv (map-distributive-trunc-product-Prop {A = A} {B = B})
  is-equiv-map-distributive-trunc-product-Prop =
    is-equiv-has-converse-is-prop
      ( is-prop-type-trunc-Prop)
      ( is-prop-product is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
      ( map-inv-distributive-trunc-product-Prop)

distributive-trunc-product-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ║ A × B ║₋₁ ≃ ║ A ║₋₁ × ║ B ║₋₁
pr1 distributive-trunc-product-Prop = map-distributive-trunc-product-Prop
pr2 distributive-trunc-product-Prop =
  is-equiv-map-distributive-trunc-product-Prop

abstract
  is-equiv-map-inv-distributive-trunc-product-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-equiv (map-inv-distributive-trunc-product-Prop {A = A} {B = B})
  is-equiv-map-inv-distributive-trunc-product-Prop =
    is-equiv-has-converse-is-prop
      ( is-prop-product is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
      ( is-prop-type-trunc-Prop)
      ( map-distributive-trunc-product-Prop)

inv-distributive-trunc-product-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ( ║ A ║₋₁ × ║ B ║₋₁) ≃ ║ A × B ║₋₁
pr1 inv-distributive-trunc-product-Prop =
  map-inv-distributive-trunc-product-Prop
pr2 inv-distributive-trunc-product-Prop =
  is-equiv-map-inv-distributive-trunc-product-Prop
```

### Propositional truncations of coproducts of types with themselves

```agda
module _
  {l : Level} {A : UU l}
  where

  map-trunc-Prop-diagonal-coproduct :
    ║ A + A ║₋₁ → ║ A ║₋₁
  map-trunc-Prop-diagonal-coproduct =
    map-universal-property-trunc-Prop
      ( trunc-Prop A)
      ( unit-trunc ∘ rec-coproduct id id)

  map-inv-trunc-Prop-diagonal-coproduct :
    ║ A ║₋₁ → ║ A + A ║₋₁
  map-inv-trunc-Prop-diagonal-coproduct =
    map-universal-property-trunc-Prop
      ( trunc-Prop (A + A))
      ( unit-trunc ∘ (inl ∘ id))

  abstract
    is-equiv-map-trunc-Prop-diagonal-coproduct :
      is-equiv map-trunc-Prop-diagonal-coproduct
    is-equiv-map-trunc-Prop-diagonal-coproduct =
      is-equiv-has-converse-is-prop
        is-prop-type-trunc-Prop
        is-prop-type-trunc-Prop
        map-inv-trunc-Prop-diagonal-coproduct

    is-equiv-map-inv-trunc-Prop-diagonal-coproduct :
      is-equiv map-inv-trunc-Prop-diagonal-coproduct
    is-equiv-map-inv-trunc-Prop-diagonal-coproduct =
      is-equiv-has-converse-is-prop
        is-prop-type-trunc-Prop
        is-prop-type-trunc-Prop
        map-trunc-Prop-diagonal-coproduct

  equiv-trunc-Prop-diagonal-coproduct :
    ║ A + A ║₋₁ ≃ ║ A ║₋₁
  pr1 equiv-trunc-Prop-diagonal-coproduct = map-trunc-Prop-diagonal-coproduct
  pr2 equiv-trunc-Prop-diagonal-coproduct =
    is-equiv-map-trunc-Prop-diagonal-coproduct

  inv-equiv-trunc-Prop-diagonal-coproduct :
    ║ A ║₋₁ ≃ ║ A + A ║₋₁
  pr1 inv-equiv-trunc-Prop-diagonal-coproduct =
    map-inv-trunc-Prop-diagonal-coproduct
  pr2 inv-equiv-trunc-Prop-diagonal-coproduct =
    is-equiv-map-inv-trunc-Prop-diagonal-coproduct
```

## `do` syntax for propositional truncation { #do-syntax }

Consider a case where you are trying to prove a proposition, `motive : Prop l`,
from witnesses of propositional truncations of types `P` and `Q`:

```text
rec-trunc-Prop
  ( motive)
  ( λ (p : P) →
    rec-trunc-Prop
      ( motive)
      ( λ (q : Q) → witness-motive-P-Q p q)
      ( witness-truncated-prop-Q p))
  ( witness-truncated-prop-P)
```

We can rewrite this using
[Agda's `do` syntax](https://agda.readthedocs.io/en/latest/language/syntactic-sugar.html#do-notation)
with the module

```agda
module do-syntax-trunc-Prop {l : Level} (motive : Prop l) where
  _>>=_ :
    {l : Level} {A : UU l} →
    type-trunc-Prop A → (A → type-Prop motive) →
    type-Prop motive
  trunc-prop-a >>= k = rec-trunc-Prop motive k trunc-prop-a
```

This allows us to rewrite the nested chain above as

```text
do
  p ← witness-truncated-prop-P
  q ← witness-truncated-prop-Q p
  witness-motive-P-Q p q
where open do-syntax-trunc-Prop motive
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [bracket type](https://ncatlab.org/nlab/show/bracket+type) at $n$Lab
