# Truncated types

```agda
module foundation-core.truncated-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.retracts-of-types
open import foundation-core.transport-along-identifications
open import foundation-core.truncation-levels
```

</details>

## Idea

The truncatedness of a type is a measure of the complexity of its identity
types. The simplest case is a contractible type. This is the base case of the
inductive definition of truncatedness for types. A type is `k+1`-truncated if
its identity types are `k`-truncated.

## Definition

### The condition of truncatedness

```agda
is-trunc : {l : Level} (k : 𝕋) → UU l → UU l
is-trunc neg-two-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (x y : A) → is-trunc k (x ＝ y)

is-trunc-eq :
  {l : Level} {k k' : 𝕋} {A : UU l} → k ＝ k' → is-trunc k A → is-trunc k' A
is-trunc-eq refl H = H
```

### The universe of truncated types

```agda
Truncated-Type : (l : Level) → 𝕋 → UU (lsuc l)
Truncated-Type l k = Σ (UU l) (is-trunc k)

module _
  {k : 𝕋} {l : Level}
  where

  type-Truncated-Type : Truncated-Type l k → UU l
  type-Truncated-Type = pr1

  is-trunc-type-Truncated-Type :
    (A : Truncated-Type l k) → is-trunc k (type-Truncated-Type A)
  is-trunc-type-Truncated-Type = pr2
```

## Properties

### If a type is `k`-truncated, then it is `k+1`-truncated

```agda
abstract
  is-trunc-succ-is-trunc :
    (k : 𝕋) {l : Level} {A : UU l} → is-trunc k A → is-trunc (succ-𝕋 k) A
  pr1 (is-trunc-succ-is-trunc neg-two-𝕋 H x y) = eq-is-contr H
  pr2 (is-trunc-succ-is-trunc neg-two-𝕋 H x .x) refl = left-inv (pr2 H x)
  is-trunc-succ-is-trunc (succ-𝕋 k) H x y = is-trunc-succ-is-trunc k (H x y)

truncated-type-succ-Truncated-Type :
  (k : 𝕋) {l : Level} → Truncated-Type l k → Truncated-Type l (succ-𝕋 k)
pr1 (truncated-type-succ-Truncated-Type k A) = type-Truncated-Type A
pr2 (truncated-type-succ-Truncated-Type k A) =
  is-trunc-succ-is-trunc k (is-trunc-type-Truncated-Type A)
```

The corollary that any `-1`-truncated type, i.e., any propoosition, is
`k+1`-truncated for any truncation level `k` is recorded in
[Propositions](foundation.propositions.md) as `is-trunc-is-prop`.

### The identity type of a `k`-truncated type is `k`-truncated

```agda
abstract
  is-trunc-Id :
    {l : Level} {k : 𝕋} {A : UU l} →
    is-trunc k A → (x y : A) → is-trunc k (x ＝ y)
  is-trunc-Id {l} {k} = is-trunc-succ-is-trunc k

Id-Truncated-Type :
  {l : Level} {k : 𝕋} (A : Truncated-Type l (succ-𝕋 k)) →
  (x y : type-Truncated-Type A) → Truncated-Type l k
pr1 (Id-Truncated-Type A x y) = (x ＝ y)
pr2 (Id-Truncated-Type A x y) = is-trunc-type-Truncated-Type A x y

Id-Truncated-Type' :
  {l : Level} {k : 𝕋} (A : Truncated-Type l k) →
  (x y : type-Truncated-Type A) → Truncated-Type l k
pr1 (Id-Truncated-Type' A x y) = (x ＝ y)
pr2 (Id-Truncated-Type' A x y) =
  is-trunc-Id (is-trunc-type-Truncated-Type A) x y
```

### `k`-truncated types are closed under retracts

```agda
module _
  {l1 l2 : Level}
  where

  is-trunc-retract-of :
    {k : 𝕋} {A : UU l1} {B : UU l2} →
    A retract-of B → is-trunc k B → is-trunc k A
  is-trunc-retract-of {neg-two-𝕋} = is-contr-retract-of _
  is-trunc-retract-of {succ-𝕋 k} R H x y =
    is-trunc-retract-of (retract-eq R x y) (H (pr1 R x) (pr1 R y))
```

### `k`-truncated types are closed under equivalences

```agda
abstract
  is-trunc-is-equiv :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} (B : UU l2) (f : A → B) → is-equiv f →
    is-trunc k B → is-trunc k A
  is-trunc-is-equiv k B f is-equiv-f =
    is-trunc-retract-of (f , (pr2 is-equiv-f))

abstract
  is-trunc-equiv :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} (B : UU l2) (e : A ≃ B) →
    is-trunc k B → is-trunc k A
  is-trunc-equiv k B (f , is-equiv-f) =
    is-trunc-is-equiv k B f is-equiv-f

abstract
  is-trunc-is-equiv' :
    {l1 l2 : Level} (k : 𝕋) (A : UU l1) {B : UU l2} (f : A → B) →
    is-equiv f → is-trunc k A → is-trunc k B
  is-trunc-is-equiv' k A f is-equiv-f is-trunc-A =
    is-trunc-is-equiv k A
      ( map-inv-is-equiv is-equiv-f)
      ( is-equiv-map-inv-is-equiv is-equiv-f)
      ( is-trunc-A)

abstract
  is-trunc-equiv' :
    {l1 l2 : Level} (k : 𝕋) (A : UU l1) {B : UU l2} (e : A ≃ B) →
    is-trunc k A → is-trunc k B
  is-trunc-equiv' k A (f , is-equiv-f) =
    is-trunc-is-equiv' k A f is-equiv-f
```

### If a type embeds into a `k+1`-truncated type, then it is `k+1`-truncated

```agda
abstract
  is-trunc-is-emb :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-emb f → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-is-emb k f Ef H x y =
    is-trunc-is-equiv k (f x ＝ f y) (ap f {x} {y}) (Ef x y) (H (f x) (f y))

abstract
  is-trunc-emb :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A ↪ B) →
    is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-emb k f = is-trunc-is-emb k (map-emb f) (is-emb-map-emb f)
```

### Truncated types are closed under dependent pair types

```agda
abstract
  is-trunc-Σ :
    {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : A → UU l2} →
    is-trunc k A → ((x : A) → is-trunc k (B x)) → is-trunc k (Σ A B)
  is-trunc-Σ {k = neg-two-𝕋} is-trunc-A is-trunc-B =
    is-contr-Σ' is-trunc-A is-trunc-B
  is-trunc-Σ {k = succ-𝕋 k} {B = B} is-trunc-A is-trunc-B s t =
    is-trunc-equiv k
      ( Σ (pr1 s ＝ pr1 t) (λ p → tr B p (pr2 s) ＝ pr2 t))
      ( equiv-pair-eq-Σ s t)
      ( is-trunc-Σ
        ( is-trunc-A (pr1 s) (pr1 t))
        ( λ p → is-trunc-B (pr1 t) (tr B p (pr2 s)) (pr2 t)))

Σ-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k)
  (B : type-Truncated-Type A → Truncated-Type l2 k) →
  Truncated-Type (l1 ⊔ l2) k
pr1 (Σ-Truncated-Type A B) =
  Σ (type-Truncated-Type A) (λ a → type-Truncated-Type (B a))
pr2 (Σ-Truncated-Type A B) =
  is-trunc-Σ
    ( is-trunc-type-Truncated-Type A)
    ( λ a → is-trunc-type-Truncated-Type (B a))

fiber-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k)
  (B : Truncated-Type l2 k)
  (f : type-Truncated-Type A → type-Truncated-Type B) →
  type-Truncated-Type B → Truncated-Type (l1 ⊔ l2) k
fiber-Truncated-Type A B f b =
  Σ-Truncated-Type A (λ a → Id-Truncated-Type' B (f a) b)
```

### Truncatedness of the base of a truncated dependent sum

```agda
abstract
  is-trunc-base-is-trunc-Σ' :
    {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : A → UU l2} →
    ((x : A) → B x) → is-trunc k (Σ A B) → is-trunc k A
  is-trunc-base-is-trunc-Σ' {k = neg-two-𝕋} {A} {B} =
    is-contr-base-is-contr-Σ' A B
  is-trunc-base-is-trunc-Σ' {k = succ-𝕋 k} s is-trunc-ΣAB x y =
    is-trunc-base-is-trunc-Σ'
      ( apd s)
      ( is-trunc-equiv' k
        ( (x , s x) ＝ (y , s y))
        ( equiv-pair-eq-Σ (x , s x) (y , s y))
        ( is-trunc-ΣAB (x , s x) (y , s y)))
```

### Products of truncated types are truncated

```agda
abstract
  is-trunc-product :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k A → is-trunc k B → is-trunc k (A × B)
  is-trunc-product k is-trunc-A is-trunc-B =
    is-trunc-Σ is-trunc-A (λ x → is-trunc-B)

product-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) →
  Truncated-Type l1 k → Truncated-Type l2 k → Truncated-Type (l1 ⊔ l2) k
pr1 (product-Truncated-Type k A B) =
  type-Truncated-Type A × type-Truncated-Type B
pr2 (product-Truncated-Type k A B) =
  is-trunc-product k
    ( is-trunc-type-Truncated-Type A)
    ( is-trunc-type-Truncated-Type B)

is-trunc-product' :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  (B → is-trunc (succ-𝕋 k) A) → (A → is-trunc (succ-𝕋 k) B) →
  is-trunc (succ-𝕋 k) (A × B)
is-trunc-product' k f g (a , b) (a' , b') =
  is-trunc-equiv k
    ( Eq-product (a , b) (a' , b'))
    ( equiv-pair-eq (a , b) (a' , b'))
    ( is-trunc-product k (f b a a') (g a b b'))

is-trunc-left-factor-product :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → B → is-trunc k A
is-trunc-left-factor-product neg-two-𝕋 {A} {B} H b =
  is-contr-left-factor-product A B H
is-trunc-left-factor-product (succ-𝕋 k) H b a a' =
  is-trunc-left-factor-product k {A = (a ＝ a')} {B = (b ＝ b)}
    ( is-trunc-equiv' k
      ( (a , b) ＝ (a' , b))
      ( equiv-pair-eq (a , b) (a' , b))
      ( H (a , b) (a' , b)))
    ( refl)

is-trunc-right-factor-product :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → A → is-trunc k B
is-trunc-right-factor-product neg-two-𝕋 {A} {B} H a =
  is-contr-right-factor-product A B H
is-trunc-right-factor-product (succ-𝕋 k) {A} {B} H a b b' =
  is-trunc-right-factor-product k {A = (a ＝ a)} {B = (b ＝ b')}
    ( is-trunc-equiv' k
      ( (a , b) ＝ (a , b'))
      ( equiv-pair-eq (a , b) (a , b'))
      ( H (a , b) (a , b')))
    ( refl)
```
