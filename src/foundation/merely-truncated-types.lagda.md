# Merely truncated types

```agda
module foundation.merely-truncated-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
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
{{#concept "merely truncated" Disambiguation="type" Agda=is-merely-trunc Agda=Merely-Truncated-Type}}
if there [exists](foundation.existential-quantification.md) some $n$ such that
$A$ is $n$-[truncated](foundation-core.truncated-types.md).

## Definition

### The condition of mere truncatedness

```agda
is-merely-trunc : {l : Level} → UU l → UU l
is-merely-trunc A = exists-structure 𝕋 (λ k → is-trunc k A)

is-prop-is-merely-trunc : {l : Level} {A : UU l} → is-prop (is-merely-trunc A)
is-prop-is-merely-trunc {A = A} = is-prop-exists 𝕋 (λ k → is-trunc-Prop k A)

is-merely-trunc-Prop : {l : Level} → UU l → Prop l
is-merely-trunc-Prop A = (is-merely-trunc A , is-prop-is-merely-trunc)
```

### The universe of merely truncated types

```agda
Merely-Truncated-Type : (l : Level) → UU (lsuc l)
Merely-Truncated-Type l = Σ (UU l) (is-merely-trunc)

type-Merely-Truncated-Type : {l : Level} → Merely-Truncated-Type l → UU l
type-Merely-Truncated-Type = pr1

is-merely-trunc-type-Merely-Truncated-Type :
  {l : Level} (A : Merely-Truncated-Type l) →
  is-merely-trunc (type-Merely-Truncated-Type A)
is-merely-trunc-type-Merely-Truncated-Type = pr2
```

## Properties

### The identity type of a merely truncated type is merely truncated

```agda
abstract
  is-merely-trunc-Id :
    {l : Level} {A : UU l} →
    is-merely-trunc A → (x y : A) → is-merely-trunc (x ＝ y)
  is-merely-trunc-Id {l} H x y = map-tot-exists (λ k H' → is-trunc-Id H' x y) H

Id-Merely-Truncated-Type :
  {l : Level} (A : Merely-Truncated-Type l) →
  (x y : type-Merely-Truncated-Type A) → Merely-Truncated-Type l
Id-Merely-Truncated-Type A x y =
  ( x ＝ y ,
    is-merely-trunc-Id (is-merely-trunc-type-Merely-Truncated-Type A) x y)
```

### Merely truncated types are closed under retracts

```agda
module _
  {l1 l2 : Level}
  where

  is-merely-trunc-retract-of :
    {A : UU l1} {B : UU l2} →
    A retract-of B → is-merely-trunc B → is-merely-trunc A
  is-merely-trunc-retract-of R = map-tot-exists (λ k → is-trunc-retract-of R)
```

### Merely truncated types are closed under equivalences

```agda
abstract
  is-merely-trunc-is-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) (f : A → B) → is-equiv f →
    is-merely-trunc B → is-merely-trunc A
  is-merely-trunc-is-equiv B f is-equiv-f =
    is-merely-trunc-retract-of (retract-equiv (f , is-equiv-f))

abstract
  is-merely-trunc-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) (e : A ≃ B) →
    is-merely-trunc B → is-merely-trunc A
  is-merely-trunc-equiv B (f , is-equiv-f) =
    is-merely-trunc-is-equiv B f is-equiv-f

abstract
  is-merely-trunc-is-equiv' :
    {l1 l2 : Level} (A : UU l1) {B : UU l2} (f : A → B) →
    is-equiv f → is-merely-trunc A → is-merely-trunc B
  is-merely-trunc-is-equiv' A f is-equiv-f is-merely-trunc-A =
    is-merely-trunc-is-equiv A
      ( map-inv-is-equiv is-equiv-f)
      ( is-equiv-map-inv-is-equiv is-equiv-f)
      ( is-merely-trunc-A)

abstract
  is-merely-trunc-equiv' :
    {l1 l2 : Level} (A : UU l1) {B : UU l2} (e : A ≃ B) →
    is-merely-trunc A → is-merely-trunc B
  is-merely-trunc-equiv' A (f , is-equiv-f) =
    is-merely-trunc-is-equiv' A f is-equiv-f
```

### If a type embeds into a merely truncated type, then it is merely truncated

There is a shorter proof that uses the fact that $n$-truncated types are
$n+1$-truncated, but we give a proof using the maximum of operation on
truncation levels in order to maintain stricter bounds on the truncation level.

```agda
abstract
  is-merely-trunc-is-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-emb f → is-merely-trunc B → is-merely-trunc A
  is-merely-trunc-is-emb {A = A} {B} f Ef =
    map-exists
      ( λ k → is-trunc k A)
      ( max-𝕋 neg-one-𝕋)
      ( λ where
        neg-two-𝕋 H → is-trunc-is-emb neg-two-𝕋 f Ef (is-prop-is-contr H)
        (succ-𝕋 k) H → is-trunc-is-emb k f Ef H)

abstract
  is-merely-trunc-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪ B) →
    is-merely-trunc B → is-merely-trunc A
  is-merely-trunc-emb f =
    is-merely-trunc-is-emb (map-emb f) (is-emb-map-emb f)
```

### Merely truncated types are closed under dependent pair types

```agda
abstract
  is-merely-trunc-Σ :
    {k : 𝕋} {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-merely-trunc A → ((x : A) → is-trunc k (B x)) →
    is-merely-trunc (Σ A B)
  is-merely-trunc-Σ {k} {A = A} {B} H K =
    map-exists
      ( λ r → is-trunc r (Σ A B))
      ( max-𝕋 k)
      ( λ r H →
        is-trunc-Σ
          ( is-trunc-right-max-𝕋 r k H)
          ( λ x → is-trunc-left-max-𝕋 k r (K x)))
      ( H)

Σ-Merely-Truncated-Type :
  {k : 𝕋} {l1 l2 : Level} (A : Merely-Truncated-Type l1)
  (B : type-Merely-Truncated-Type A → Truncated-Type l2 k) →
  Merely-Truncated-Type (l1 ⊔ l2)
pr1 (Σ-Merely-Truncated-Type A B) =
  Σ (type-Merely-Truncated-Type A) (type-Truncated-Type ∘ B)
pr2 (Σ-Merely-Truncated-Type A B) =
  is-merely-trunc-Σ
    ( is-merely-trunc-type-Merely-Truncated-Type A)
    ( λ a → is-trunc-type-Truncated-Type (B a))

fiber-Merely-Truncated-Type :
  {k : 𝕋} {l1 l2 : Level} (A : Merely-Truncated-Type l1)
  (B : Truncated-Type l2 k)
  (f : type-Merely-Truncated-Type A → type-Truncated-Type B) →
  type-Truncated-Type B → Merely-Truncated-Type (l1 ⊔ l2)
fiber-Merely-Truncated-Type A B f b =
  Σ-Merely-Truncated-Type A (λ a → Id-Truncated-Type' B (f a) b)
```

### Mere truncatedness of the base of a merely truncated dependent sum

```agda
abstract
  is-merely-trunc-base-is-merely-trunc-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → B x) → is-merely-trunc (Σ A B) → is-merely-trunc A
  is-merely-trunc-base-is-merely-trunc-Σ' f =
    map-tot-exists (λ k → is-trunc-base-is-trunc-Σ' f)
```

### Products of merely truncated types are truncated

```agda
abstract
  is-merely-trunc-product :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-merely-trunc A → is-merely-trunc B → is-merely-trunc (A × B)
  is-merely-trunc-product {A = A} {B} =
    map-binary-exists
      ( λ k → is-trunc k (A × B))
      ( max-𝕋)
      ( λ k r K R →
        is-trunc-product
          ( max-𝕋 k r)
          ( is-trunc-left-max-𝕋 k r K)
          ( is-trunc-right-max-𝕋 r k R))

product-Merely-Truncated-Type :
  {l1 l2 : Level} →
  Merely-Truncated-Type l1 →
  Merely-Truncated-Type l2 →
  Merely-Truncated-Type (l1 ⊔ l2)
pr1 (product-Merely-Truncated-Type A B) =
  type-Merely-Truncated-Type A × type-Merely-Truncated-Type B
pr2 (product-Merely-Truncated-Type A B) =
  is-merely-trunc-product
    ( is-merely-trunc-type-Merely-Truncated-Type A)
    ( is-merely-trunc-type-Merely-Truncated-Type B)
```

### The type of functions into a truncated type is truncated

```agda
abstract
  is-merely-trunc-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-merely-trunc B → is-merely-trunc (A → B)
  is-merely-trunc-function-type {A} {B} =
    map-tot-exists (λ k → is-trunc-function-type k)

function-type-Merely-Truncated-Type :
  {l1 l2 : Level} (A : UU l1) (B : Merely-Truncated-Type l2) →
  Merely-Truncated-Type (l1 ⊔ l2)
function-type-Merely-Truncated-Type A B =
  ( ( A → type-Merely-Truncated-Type B) ,
    ( is-merely-trunc-function-type
      ( is-merely-trunc-type-Merely-Truncated-Type B)))

type-hom-Merely-Truncated-Type :
  {l1 l2 : Level} (A : Merely-Truncated-Type l1)
  (B : Merely-Truncated-Type l2) → UU (l1 ⊔ l2)
type-hom-Merely-Truncated-Type A B =
  type-Merely-Truncated-Type A → type-Merely-Truncated-Type B

is-merely-trunc-type-hom-Merely-Truncated-Type :
  {l1 l2 : Level} (A : Merely-Truncated-Type l1)
  (B : Merely-Truncated-Type l2) →
  is-merely-trunc (type-hom-Merely-Truncated-Type A B)
is-merely-trunc-type-hom-Merely-Truncated-Type A B =
  is-merely-trunc-function-type (is-merely-trunc-type-Merely-Truncated-Type B)

hom-Merely-Truncated-Type :
  {l1 l2 : Level} (A : Merely-Truncated-Type l1)
  (B : Merely-Truncated-Type l2) → Merely-Truncated-Type (l1 ⊔ l2)
hom-Merely-Truncated-Type A B =
  ( type-hom-Merely-Truncated-Type A B ,
    is-merely-trunc-type-hom-Merely-Truncated-Type A B)
```

### The coproduct type is merely truncated

```agda
abstract
  is-merely-trunc-coproduct :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-merely-trunc A → is-merely-trunc B → is-merely-trunc (A + B)
  is-merely-trunc-coproduct {A = A} {B} =
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

  is-merely-trunc-equiv-is-merely-trunc :
    is-merely-trunc A → is-merely-trunc B → is-merely-trunc (A ≃ B)
  is-merely-trunc-equiv-is-merely-trunc =
    map-binary-exists
      ( λ k → is-trunc k (A ≃ B))
      ( max-𝕋)
      ( λ k r K R →
        is-trunc-equiv-is-trunc
          ( max-𝕋 k r)
          ( is-trunc-left-max-𝕋 k r K)
          ( is-trunc-right-max-𝕋 r k R))

type-equiv-Merely-Truncated-Type :
  {l1 l2 : Level} → Merely-Truncated-Type l1 → Merely-Truncated-Type l2 →
  UU (l1 ⊔ l2)
type-equiv-Merely-Truncated-Type A B =
  type-Merely-Truncated-Type A ≃ type-Merely-Truncated-Type B

is-merely-trunc-type-equiv-Merely-Truncated-Type :
  {l1 l2 : Level}
  (A : Merely-Truncated-Type l1) (B : Merely-Truncated-Type l2) →
  is-merely-trunc (type-equiv-Merely-Truncated-Type A B)
is-merely-trunc-type-equiv-Merely-Truncated-Type A B =
  is-merely-trunc-equiv-is-merely-trunc
    ( is-merely-trunc-type-Merely-Truncated-Type A)
    ( is-merely-trunc-type-Merely-Truncated-Type B)

equiv-Merely-Truncated-Type :
  {l1 l2 : Level} → Merely-Truncated-Type l1 → Merely-Truncated-Type l2 →
  Merely-Truncated-Type (l1 ⊔ l2)
equiv-Merely-Truncated-Type A B =
  ( type-equiv-Merely-Truncated-Type A B ,
    is-merely-trunc-type-equiv-Merely-Truncated-Type A B)
```
