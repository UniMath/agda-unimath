# Truncated types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.truncated-types where

open import foundation-core.truncated-types public

open import foundation-core.cartesian-product-types using (_×_)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.embeddings using
  ( is-emb; _↪_; map-emb; is-emb-map-emb)
open import foundation-core.equality-cartesian-product-types using
  ( Eq-prod; equiv-pair-eq)
open import foundation-core.equality-dependent-pair-types using
  ( equiv-pair-eq-Σ)
open import foundation-core.equivalences using (_≃_; map-equiv)
open import foundation-core.homotopies using (_~_)
open import foundation-core.identity-types using (Id; refl; ap; tr)
open import foundation-core.propositions using (is-prop)
open import foundation-core.retractions using (_retract-of_)
open import foundation-core.truncation-levels using
  ( 𝕋; neg-two-𝕋; neg-one-𝕋; succ-𝕋)
open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.contractible-types using
  ( is-contr-Σ'; is-contr-left-factor-prod; is-contr-right-factor-prod;
    is-contr-Π; is-subtype-is-contr; is-contr-equiv-is-contr)
open import foundation.equivalences-with-function-extensionality using
  ( htpy-equiv; extensionality-equiv)
open import foundation.function-extensionality using (htpy-eq; funext)
```

## Properties

### If a type embeds into a (k+1)-truncated type, then it is (k+1)-truncated

```agda
abstract
  is-trunc-is-emb :
    {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} (f : A → B) →
    is-emb f → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-is-emb k f Ef H x y =
    is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y}) (Ef x y) (H (f x) (f y))

abstract
  is-trunc-emb :
    {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} (f : A ↪ B) →
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
      ( Σ (Id (pr1 s) (pr1 t)) (λ p → Id (tr B p (pr2 s)) (pr2 t)))
      ( equiv-pair-eq-Σ s t)
      ( is-trunc-Σ
        ( is-trunc-A (pr1 s) (pr1 t))
        ( λ p → is-trunc-B (pr1 t) (tr B p (pr2 s)) (pr2 t)))

Σ-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : UU-Truncated-Type k l1)
  (B : type-Truncated-Type A → UU-Truncated-Type k l2) →
  UU-Truncated-Type k (l1 ⊔ l2)
pr1 (Σ-Truncated-Type A B) =
  Σ (type-Truncated-Type A) (λ a → type-Truncated-Type (B a))
pr2 (Σ-Truncated-Type A B) =
  is-trunc-Σ
    ( is-trunc-type-Truncated-Type A)
    ( λ a → is-trunc-type-Truncated-Type (B a))

fib-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : UU-Truncated-Type k l1)
  (B : UU-Truncated-Type k l2)
  (f : type-Truncated-Type A → type-Truncated-Type B) →
  type-Truncated-Type B → UU-Truncated-Type k (l1 ⊔ l2)
fib-Truncated-Type A B f b =
  Σ-Truncated-Type A (λ a → Id-Truncated-Type' B (f a) b)
```

### Products of truncated types are truncated

```agda
abstract
  is-trunc-prod :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k A → is-trunc k B → is-trunc k (A × B)
  is-trunc-prod k is-trunc-A is-trunc-B =
    is-trunc-Σ is-trunc-A (λ x → is-trunc-B)

is-trunc-prod' :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  (B → is-trunc (succ-𝕋 k) A) → (A → is-trunc (succ-𝕋 k) B) →
  is-trunc (succ-𝕋 k) (A × B)
is-trunc-prod' k f g (pair a b) (pair a' b') =
  is-trunc-equiv k
    ( Eq-prod (pair a b) (pair a' b'))
    ( equiv-pair-eq (pair a b) (pair a' b'))
    ( is-trunc-prod k (f b a a') (g a b b'))

is-trunc-left-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → B → is-trunc k A
is-trunc-left-factor-prod neg-two-𝕋 {A} {B} H b =
  is-contr-left-factor-prod A B H
is-trunc-left-factor-prod (succ-𝕋 k) H b a a' =
  is-trunc-left-factor-prod k {A = Id a a'} {B = Id b b}
    ( is-trunc-equiv' k
      ( Id (pair a b) (pair a' b))
      ( equiv-pair-eq (pair a b) (pair a' b))
      ( H (pair a b) (pair a' b)))
    ( refl)

is-trunc-right-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → A → is-trunc k B
is-trunc-right-factor-prod neg-two-𝕋 {A} {B} H a =
  is-contr-right-factor-prod A B H
is-trunc-right-factor-prod (succ-𝕋 k) {A} {B} H a b b' =
  is-trunc-right-factor-prod k {A = Id a a} {B = Id b b'}
    ( is-trunc-equiv' k
      ( Id (pair a b) (pair a b'))
      ( equiv-pair-eq (pair a b) (pair a b'))
      ( H (pair a b) (pair a b')))
    ( refl)
```

### Products of families of truncated types are truncated

```agda
abstract
  is-trunc-Π :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-trunc k (B x)) → is-trunc k ((x : A) → B x)
  is-trunc-Π neg-two-𝕋 is-trunc-B = is-contr-Π is-trunc-B
  is-trunc-Π (succ-𝕋 k) is-trunc-B f g =
    is-trunc-is-equiv k (f ~ g) htpy-eq
      ( funext f g)
      ( is-trunc-Π k (λ x → is-trunc-B x (f x) (g x)))

type-Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → UU-Truncated-Type k l2) →
  UU (l1 ⊔ l2)
type-Π-Truncated-Type' k A B = (x : A) → type-Truncated-Type (B x)

is-trunc-type-Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → UU-Truncated-Type k l2) →
  is-trunc k (type-Π-Truncated-Type' k A B)
is-trunc-type-Π-Truncated-Type' k A B =
  is-trunc-Π k (λ x → is-trunc-type-Truncated-Type (B x))

Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → UU-Truncated-Type k l2) →
  UU-Truncated-Type k (l1 ⊔ l2)
pr1 (Π-Truncated-Type' k A B) = type-Π-Truncated-Type' k A B
pr2 (Π-Truncated-Type' k A B) = is-trunc-type-Π-Truncated-Type' k A B

type-Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : type-Truncated-Type A → UU-Truncated-Type k l2) →
  UU (l1 ⊔ l2)
type-Π-Truncated-Type k A B =
  type-Π-Truncated-Type' k (type-Truncated-Type A) B

is-trunc-type-Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : type-Truncated-Type A → UU-Truncated-Type k l2) →
  is-trunc k (type-Π-Truncated-Type k A B)
is-trunc-type-Π-Truncated-Type k A B =
  is-trunc-type-Π-Truncated-Type' k (type-Truncated-Type A) B

Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : type-Truncated-Type A → UU-Truncated-Type k l2) →
  UU-Truncated-Type k (l1 ⊔ l2)
Π-Truncated-Type k A B =
  Π-Truncated-Type' k (type-Truncated-Type A) B
```

### The type of functions into a truncated type is truncated

```agda
abstract
  is-trunc-function-type :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k B → is-trunc k (A → B)
  is-trunc-function-type k {A} {B} is-trunc-B =
    is-trunc-Π k {B = λ (x : A) → B} (λ x → is-trunc-B)

type-hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : UU-Truncated-Type k l2) → UU (l1 ⊔ l2)
type-hom-Truncated-Type k A B =
  type-Truncated-Type A → type-Truncated-Type B

is-trunc-type-hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : UU-Truncated-Type k l2) →
  is-trunc k (type-hom-Truncated-Type k A B)
is-trunc-type-hom-Truncated-Type k A B =
  is-trunc-function-type k (is-trunc-type-Truncated-Type B)

hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : UU-Truncated-Type k l2) → UU-Truncated-Type k (l1 ⊔ l2)
pr1 (hom-Truncated-Type k A B) = type-hom-Truncated-Type k A B
pr2 (hom-Truncated-Type k A B) = is-trunc-type-hom-Truncated-Type k A B
```

### Being truncated is a property

```agda
abstract
  is-prop-is-trunc :
    {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-trunc k A)
  is-prop-is-trunc neg-two-𝕋 A = is-subtype-is-contr
  is-prop-is-trunc (succ-𝕋 k) A =
    is-trunc-Π neg-one-𝕋
      ( λ x → is-trunc-Π neg-one-𝕋 (λ y → is-prop-is-trunc k (Id x y)))

is-trunc-Prop : {l : Level} (k : 𝕋) (A : UU l) → Σ (UU l) (is-trunc neg-one-𝕋)
pr1 (is-trunc-Prop k A) = is-trunc k A
pr2 (is-trunc-Prop k A) = is-prop-is-trunc k A
```

### The type of equivalences between truncated types is truncated

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-trunc-equiv-is-trunc :
    (k : 𝕋) → is-trunc k A → is-trunc k B → is-trunc k (A ≃ B)
  is-trunc-equiv-is-trunc neg-two-𝕋 is-trunc-A is-trunc-B =
    is-contr-equiv-is-contr is-trunc-A is-trunc-B
  is-trunc-equiv-is-trunc (succ-𝕋 k) is-trunc-A is-trunc-B f g =
    is-trunc-equiv k
      ( htpy-equiv f g)
      ( extensionality-equiv f g)
      ( is-trunc-Π k (λ x → is-trunc-B (map-equiv f x) (map-equiv g x)))
```
