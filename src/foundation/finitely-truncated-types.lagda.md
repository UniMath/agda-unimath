# Finitely truncated types

```agda
module foundation.finitely-truncated-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-truncated-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.maximum-truncation-levels
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retracts-of-types
open import foundation-core.transport-along-identifications

open import logic.functoriality-existential-quantification
```

</details>

## Idea

A type $A$ is
{{#concept "finitely truncated" Disambiguation="type" Agda=is-finitely-trunc Agda=Finitely-Truncated-Type}}
if there [exists](foundation.existential-quantification.md) some $n$ such that
$A$ is $n$-[truncated](foundation-core.truncated-types.md).

## Definition

### The condition of being finitely truncated

```agda
is-finitely-trunc : {l : Level} → UU l → UU l
is-finitely-trunc A = exists-structure 𝕋 (λ k → is-trunc k A)

is-prop-is-finitely-trunc :
  {l : Level} {A : UU l} → is-prop (is-finitely-trunc A)
is-prop-is-finitely-trunc {A = A} = is-prop-exists 𝕋 (λ k → is-trunc-Prop k A)

is-finitely-trunc-Prop : {l : Level} → UU l → Prop l
is-finitely-trunc-Prop A = (is-finitely-trunc A , is-prop-is-finitely-trunc)
```

### The universe of finitely truncated types

```agda
Finitely-Truncated-Type : (l : Level) → UU (lsuc l)
Finitely-Truncated-Type l = Σ (UU l) (is-finitely-trunc)

type-Finitely-Truncated-Type : {l : Level} → Finitely-Truncated-Type l → UU l
type-Finitely-Truncated-Type = pr1

is-finitely-trunc-type-Finitely-Truncated-Type :
  {l : Level} (A : Finitely-Truncated-Type l) →
  is-finitely-trunc (type-Finitely-Truncated-Type A)
is-finitely-trunc-type-Finitely-Truncated-Type = pr2
```

## Properties

### The identity type of a finitely truncated type is finitely truncated

```agda
abstract
  is-finitely-trunc-Id :
    {l : Level} {A : UU l} →
    is-finitely-trunc A → (x y : A) → is-finitely-trunc (x ＝ y)
  is-finitely-trunc-Id {l} H x y =
    map-tot-exists (λ k H' → is-trunc-Id H' x y) H

Id-Finitely-Truncated-Type :
  {l : Level} (A : Finitely-Truncated-Type l) →
  (x y : type-Finitely-Truncated-Type A) → Finitely-Truncated-Type l
Id-Finitely-Truncated-Type A x y =
  ( x ＝ y ,
    is-finitely-trunc-Id (is-finitely-trunc-type-Finitely-Truncated-Type A) x y)
```

### Finitely truncated types are closed under retracts

```agda
module _
  {l1 l2 : Level}
  where

  is-finitely-trunc-retract-of :
    {A : UU l1} {B : UU l2} →
    A retract-of B → is-finitely-trunc B → is-finitely-trunc A
  is-finitely-trunc-retract-of R = map-tot-exists (λ k → is-trunc-retract-of R)
```

### Finitely truncated types are closed under equivalences

```agda
abstract
  is-finitely-trunc-is-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) (f : A → B) → is-equiv f →
    is-finitely-trunc B → is-finitely-trunc A
  is-finitely-trunc-is-equiv B f is-equiv-f =
    is-finitely-trunc-retract-of (retract-equiv (f , is-equiv-f))

abstract
  is-finitely-trunc-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) (e : A ≃ B) →
    is-finitely-trunc B → is-finitely-trunc A
  is-finitely-trunc-equiv B (f , is-equiv-f) =
    is-finitely-trunc-is-equiv B f is-equiv-f

abstract
  is-finitely-trunc-is-equiv' :
    {l1 l2 : Level} (A : UU l1) {B : UU l2} (f : A → B) →
    is-equiv f → is-finitely-trunc A → is-finitely-trunc B
  is-finitely-trunc-is-equiv' A f is-equiv-f is-finitely-trunc-A =
    is-finitely-trunc-is-equiv A
      ( map-inv-is-equiv is-equiv-f)
      ( is-equiv-map-inv-is-equiv is-equiv-f)
      ( is-finitely-trunc-A)

abstract
  is-finitely-trunc-equiv' :
    {l1 l2 : Level} (A : UU l1) {B : UU l2} (e : A ≃ B) →
    is-finitely-trunc A → is-finitely-trunc B
  is-finitely-trunc-equiv' A (f , is-equiv-f) =
    is-finitely-trunc-is-equiv' A f is-equiv-f
```

### If a type embeds into a finitely truncated type, then it is finitely truncated

There is a shorter proof that uses the fact that $n$-truncated types are
$n+1$-truncated, but we give a proof using the maximum of operation on
truncation levels in order to maintain stricter bounds on the truncation level.

```agda
abstract
  is-finitely-trunc-is-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-emb f → is-finitely-trunc B → is-finitely-trunc A
  is-finitely-trunc-is-emb {A = A} {B} f Ef =
    map-exists
      ( λ k → is-trunc k A)
      ( max-𝕋 neg-one-𝕋)
      ( λ where
        neg-two-𝕋 H → is-trunc-is-emb neg-two-𝕋 f Ef (is-prop-is-contr H)
        (succ-𝕋 k) H → is-trunc-is-emb k f Ef H)

abstract
  is-finitely-trunc-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪ B) →
    is-finitely-trunc B → is-finitely-trunc A
  is-finitely-trunc-emb f =
    is-finitely-trunc-is-emb (map-emb f) (is-emb-map-emb f)
```

### Finitely truncated types are closed under dependent pair types

```agda
abstract
  is-finitely-trunc-Σ :
    {k : 𝕋} {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-finitely-trunc A → ((x : A) → is-trunc k (B x)) →
    is-finitely-trunc (Σ A B)
  is-finitely-trunc-Σ {k} {A = A} {B} H K =
    map-exists
      ( λ r → is-trunc r (Σ A B))
      ( max-𝕋 k)
      ( λ r H →
        is-trunc-Σ
          ( is-trunc-right-max-𝕋 r k H)
          ( λ x → is-trunc-left-max-𝕋 k r (K x)))
      ( H)

Σ-Finitely-Truncated-Type :
  {k : 𝕋} {l1 l2 : Level} (A : Finitely-Truncated-Type l1)
  (B : type-Finitely-Truncated-Type A → Truncated-Type l2 k) →
  Finitely-Truncated-Type (l1 ⊔ l2)
pr1 (Σ-Finitely-Truncated-Type A B) =
  Σ (type-Finitely-Truncated-Type A) (type-Truncated-Type ∘ B)
pr2 (Σ-Finitely-Truncated-Type A B) =
  is-finitely-trunc-Σ
    ( is-finitely-trunc-type-Finitely-Truncated-Type A)
    ( λ a → is-trunc-type-Truncated-Type (B a))

fiber-Finitely-Truncated-Type :
  {k : 𝕋} {l1 l2 : Level} (A : Finitely-Truncated-Type l1)
  (B : Truncated-Type l2 k)
  (f : type-Finitely-Truncated-Type A → type-Truncated-Type B) →
  type-Truncated-Type B → Finitely-Truncated-Type (l1 ⊔ l2)
fiber-Finitely-Truncated-Type A B f b =
  Σ-Finitely-Truncated-Type A (λ a → Id-Truncated-Type' B (f a) b)
```

### Finite truncatedness of the base of a finitely truncated dependent sum

```agda
abstract
  is-finitely-trunc-base-is-finitely-trunc-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → B x) → is-finitely-trunc (Σ A B) → is-finitely-trunc A
  is-finitely-trunc-base-is-finitely-trunc-Σ' f =
    map-tot-exists (λ k → is-trunc-base-is-trunc-Σ' f)
```

### Products of finitely truncated types are truncated

```agda
abstract
  is-finitely-trunc-product :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finitely-trunc A → is-finitely-trunc B → is-finitely-trunc (A × B)
  is-finitely-trunc-product {A = A} {B} =
    map-binary-exists
      ( λ k → is-trunc k (A × B))
      ( max-𝕋)
      ( λ k r K R →
        is-trunc-product
          ( max-𝕋 k r)
          ( is-trunc-left-max-𝕋 k r K)
          ( is-trunc-right-max-𝕋 r k R))

product-Finitely-Truncated-Type :
  {l1 l2 : Level} →
  Finitely-Truncated-Type l1 →
  Finitely-Truncated-Type l2 →
  Finitely-Truncated-Type (l1 ⊔ l2)
pr1 (product-Finitely-Truncated-Type A B) =
  type-Finitely-Truncated-Type A × type-Finitely-Truncated-Type B
pr2 (product-Finitely-Truncated-Type A B) =
  is-finitely-trunc-product
    ( is-finitely-trunc-type-Finitely-Truncated-Type A)
    ( is-finitely-trunc-type-Finitely-Truncated-Type B)
```

### The type of functions into a truncated type is truncated

```agda
abstract
  is-finitely-trunc-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finitely-trunc B → is-finitely-trunc (A → B)
  is-finitely-trunc-function-type {A} {B} =
    map-tot-exists (λ k → is-trunc-function-type k)

function-type-Finitely-Truncated-Type :
  {l1 l2 : Level} (A : UU l1) (B : Finitely-Truncated-Type l2) →
  Finitely-Truncated-Type (l1 ⊔ l2)
function-type-Finitely-Truncated-Type A B =
  ( ( A → type-Finitely-Truncated-Type B) ,
    ( is-finitely-trunc-function-type
      ( is-finitely-trunc-type-Finitely-Truncated-Type B)))

type-hom-Finitely-Truncated-Type :
  {l1 l2 : Level} (A : Finitely-Truncated-Type l1)
  (B : Finitely-Truncated-Type l2) → UU (l1 ⊔ l2)
type-hom-Finitely-Truncated-Type A B =
  type-Finitely-Truncated-Type A → type-Finitely-Truncated-Type B

is-finitely-trunc-type-hom-Finitely-Truncated-Type :
  {l1 l2 : Level} (A : Finitely-Truncated-Type l1)
  (B : Finitely-Truncated-Type l2) →
  is-finitely-trunc (type-hom-Finitely-Truncated-Type A B)
is-finitely-trunc-type-hom-Finitely-Truncated-Type A B =
  is-finitely-trunc-function-type
    ( is-finitely-trunc-type-Finitely-Truncated-Type B)

hom-Finitely-Truncated-Type :
  {l1 l2 : Level} (A : Finitely-Truncated-Type l1)
  (B : Finitely-Truncated-Type l2) → Finitely-Truncated-Type (l1 ⊔ l2)
hom-Finitely-Truncated-Type A B =
  ( type-hom-Finitely-Truncated-Type A B ,
    is-finitely-trunc-type-hom-Finitely-Truncated-Type A B)
```

### The coproduct type is finitely truncated

```agda
abstract
  is-finitely-trunc-coproduct :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finitely-trunc A → is-finitely-trunc B → is-finitely-trunc (A + B)
  is-finitely-trunc-coproduct {A = A} {B} =
    map-binary-exists
      ( λ k → is-trunc k (A + B))
      ( λ k r → succ-𝕋 (succ-𝕋 (k ⊔𝕋 r)))
      ( λ k r K R →
        is-trunc-coproduct
          ( k ⊔𝕋 r)
          ( is-trunc-iterated-succ-is-trunc
            ( max-𝕋 k r)
            ( 2)
            ( is-trunc-left-max-𝕋 k r K))
          ( is-trunc-iterated-succ-is-trunc
            ( max-𝕋 k r)
            ( 2)
            ( is-trunc-right-max-𝕋 r k R)))
```

Note that the bound on the truncation level in the preceding proof is not
optimal.

### The type of equivalences between truncated types is truncated

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-finitely-trunc-equiv-is-finitely-trunc :
    is-finitely-trunc A → is-finitely-trunc B → is-finitely-trunc (A ≃ B)
  is-finitely-trunc-equiv-is-finitely-trunc =
    map-binary-exists
      ( λ k → is-trunc k (A ≃ B))
      ( max-𝕋)
      ( λ k r K R →
        is-trunc-equiv-is-trunc
          ( max-𝕋 k r)
          ( is-trunc-left-max-𝕋 k r K)
          ( is-trunc-right-max-𝕋 r k R))

type-equiv-Finitely-Truncated-Type :
  {l1 l2 : Level} → Finitely-Truncated-Type l1 → Finitely-Truncated-Type l2 →
  UU (l1 ⊔ l2)
type-equiv-Finitely-Truncated-Type A B =
  type-Finitely-Truncated-Type A ≃ type-Finitely-Truncated-Type B

is-finitely-trunc-type-equiv-Finitely-Truncated-Type :
  {l1 l2 : Level}
  (A : Finitely-Truncated-Type l1) (B : Finitely-Truncated-Type l2) →
  is-finitely-trunc (type-equiv-Finitely-Truncated-Type A B)
is-finitely-trunc-type-equiv-Finitely-Truncated-Type A B =
  is-finitely-trunc-equiv-is-finitely-trunc
    ( is-finitely-trunc-type-Finitely-Truncated-Type A)
    ( is-finitely-trunc-type-Finitely-Truncated-Type B)

equiv-Finitely-Truncated-Type :
  {l1 l2 : Level} → Finitely-Truncated-Type l1 → Finitely-Truncated-Type l2 →
  Finitely-Truncated-Type (l1 ⊔ l2)
equiv-Finitely-Truncated-Type A B =
  ( type-equiv-Finitely-Truncated-Type A B ,
    is-finitely-trunc-type-equiv-Finitely-Truncated-Type A B)
```
