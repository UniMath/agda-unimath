# Weak function extensionality

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.weak-function-extensionality where

open import foundation.1-types using
  ( is-1-type; UU-1-Type; type-1-Type; is-1-type-type-1-Type)
open import foundation.contractible-types using
  ( is-contr; center; contraction; is-contr-retract-of; is-contr-total-path)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using
  ( is-prop-empty; is-empty)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using
  ( map-inv-is-equiv; _≃_; is-equiv; is-equiv-has-inverse)
open import foundation.function-extensionality using
  ( FUNEXT; htpy-eq; funext)
open import foundation.functions using (_∘_; id)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl; inv; _∙_)
open import foundation.negation using (¬)
open import foundation.propositions using
  ( is-prop; is-prop-equiv; UU-Prop; type-Prop; is-prop-type-Prop)
open import foundation.sets using (is-set; UU-Set; type-Set; is-set-type-Set)
open import foundation.subtypes using (is-subtype)
open import foundation.truncated-types using
  ( is-trunc; is-trunc-is-equiv; UU-Truncated-Type; type-Truncated-Type;
    is-trunc-type-Truncated-Type)
open import foundation.truncation-levels using
  ( 𝕋; neg-two-𝕋; neg-one-𝕋; zero-𝕋; one-𝕋; succ-𝕋)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

Weak function extensionality is the principle that any dependent product of contractible types is contractible. This principle is equivalent to the function extensionality axiom.

## Definition

```agda
WEAK-FUNEXT :
  {i j : Level} (A : UU i) (B : A → UU j) → UU (i ⊔ j)
WEAK-FUNEXT A B =
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
```

## Properties

### Weak function extensionality is logically equivalent to function extensionality

```agda
abstract
  WEAK-FUNEXT-FUNEXT :
    {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f) →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B)
  pr1 (WEAK-FUNEXT-FUNEXT funext A B is-contr-B) x = center (is-contr-B x)
  pr2 (WEAK-FUNEXT-FUNEXT funext A B is-contr-B) f =
    map-inv-is-equiv (funext A B c f) (λ x → contraction (is-contr-B x) (f x))
    where
    c : (x : A) → B x
    c x = center (is-contr-B x)

abstract
  FUNEXT-WEAK-FUNEXT :
    {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B) →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f)
  FUNEXT-WEAK-FUNEXT weak-funext A B f =
    fundamental-theorem-id f
      ( refl-htpy)
      ( is-contr-retract-of
        ( (x : A) → Σ (B x) (λ b → Id (f x) b))
        ( pair
          ( λ t x → pair (pr1 t x) (pr2 t x))
          ( pair (λ t → pair (λ x → pr1 (t x)) (λ x → pr2 (t x)))
          ( λ t → eq-pair-Σ refl refl)))
        ( weak-funext A
          ( λ x → Σ (B x) (λ b → Id (f x) b))
          ( λ x → is-contr-total-path (f x))))
      ( λ g → htpy-eq {g = g})
```

### Products of families of contractible types are contractible

Since we assumed function extensionality, we can conclude weak function extensionality.

```agda
abstract
  is-contr-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
  is-contr-Π {A = A} {B = B} = WEAK-FUNEXT-FUNEXT (λ X Y → funext) A B
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

### Products of families of propositions are propositions

```agda
abstract
  is-prop-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-subtype B → is-prop ((x : A) → B x)
  is-prop-Π = is-trunc-Π neg-one-𝕋

type-Π-Prop :
  {l1 l2 : Level} (A : UU l1) (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
type-Π-Prop A P = (x : A) → type-Prop (P x)

is-prop-type-Π-Prop :
  {l1 l2 : Level} (A : UU l1) (P : A → UU-Prop l2) → is-prop (type-Π-Prop A P)
is-prop-type-Π-Prop A P = is-prop-Π (λ x → is-prop-type-Prop (P x))

Π-Prop :
  {l1 l2 : Level} (A : UU l1) →
  (A → UU-Prop l2) → UU-Prop (l1 ⊔ l2)
pr1 (Π-Prop A P) = type-Π-Prop A P
pr2 (Π-Prop A P) = is-prop-type-Π-Prop A P
```

We repeat the above for implicit Π-types.

```agda
abstract
  is-prop-Π' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-subtype B → is-prop ({x : A} → B x)
  is-prop-Π' {l1} {l2} {A} {B} H =
    is-prop-equiv
      ( pair
        ( λ f x → f {x})
        ( is-equiv-has-inverse
          ( λ g {x} → g x)
          ( refl-htpy)
          ( refl-htpy)))
      ( is-prop-Π H)

type-Π-Prop' :
  {l1 l2 : Level} (A : UU l1) (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
type-Π-Prop' A P = {x : A} → type-Prop (P x)

is-prop-type-Π-Prop' :
  {l1 l2 : Level} (A : UU l1) (P : A → UU-Prop l2) → is-prop (type-Π-Prop' A P)
is-prop-type-Π-Prop' A P = is-prop-Π' (λ x → is-prop-type-Prop (P x))

Π-Prop' : {l1 l2 : Level} (A : UU l1) (P : A → UU-Prop l2) → UU-Prop (l1 ⊔ l2)
pr1 (Π-Prop' A P) = {x : A} → type-Prop (P x)
pr2 (Π-Prop' A P) = is-prop-Π' (λ x → is-prop-type-Prop (P x))
```

### Products of families of sets are sets

```agda
abstract
  is-set-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-set (B x)) → is-set ((x : A) → (B x))
  is-set-Π = is-trunc-Π zero-𝕋

type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → UU (l1 ⊔ l2)
type-Π-Set' A B = (x : A) → type-Set (B x)

is-set-type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → is-set (type-Π-Set' A B)
is-set-type-Π-Set' A B =
  is-set-Π (λ x → is-set-type-Set (B x))

Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → UU-Set (l1 ⊔ l2)
pr1 (Π-Set' A B) = type-Π-Set' A B
pr2 (Π-Set' A B) = is-set-type-Π-Set' A B

type-Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : type-Set A → UU-Set l2) → UU (l1 ⊔ l2)
type-Π-Set A B = type-Π-Set' (type-Set A) B

is-set-type-Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : type-Set A → UU-Set l2) →
  is-set (type-Π-Set A B)
is-set-type-Π-Set A B =
  is-set-type-Π-Set' (type-Set A) B

Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) →
  (type-Set A → UU-Set l2) → UU-Set (l1 ⊔ l2)
pr1 (Π-Set A B) = type-Π-Set A B
pr2 (Π-Set A B) = is-set-type-Π-Set A B
```

### Products of families of 1-types are 1-types

```agda
abstract
  is-1-type-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-1-type (B x)) → is-1-type ((x : A) → B x)
  is-1-type-Π = is-trunc-Π one-𝕋

type-Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-1-Type l2) → UU (l1 ⊔ l2)
type-Π-1-Type' A B = (x : A) → type-1-Type (B x)

is-1-type-type-Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-1-Type l2) →
  is-1-type (type-Π-1-Type' A B)
is-1-type-type-Π-1-Type' A B =
  is-1-type-Π (λ x → is-1-type-type-1-Type (B x))

Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-1-Type l2) → UU-1-Type (l1 ⊔ l2)
pr1 (Π-1-Type' A B) = type-Π-1-Type' A B
pr2 (Π-1-Type' A B) = is-1-type-type-Π-1-Type' A B

type-Π-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU-1-Type l2) →
  UU (l1 ⊔ l2)
type-Π-1-Type A B = type-Π-1-Type' (type-1-Type A) B

is-1-type-type-Π-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU-1-Type l2) →
  is-1-type (type-Π-1-Type A B)
is-1-type-type-Π-1-Type A B =
  is-1-type-type-Π-1-Type' (type-1-Type A) B

Π-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU-1-Type l2) →
  UU-1-Type (l1 ⊔ l2)
pr1 (Π-1-Type A B) = type-Π-1-Type A B
pr2 (Π-1-Type A B) = is-1-type-type-Π-1-Type A B
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

### The type of functions into a proposition is a proposition

```agda
abstract
  is-prop-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop B → is-prop (A → B)
  is-prop-function-type = is-trunc-function-type neg-one-𝕋

type-function-Prop :
  {l1 l2 : Level} → UU l1 → UU-Prop l2 → UU (l1 ⊔ l2)
type-function-Prop A P = A → type-Prop P

is-prop-type-function-Prop :
  {l1 l2 : Level} (A : UU l1) (P : UU-Prop l2) →
  is-prop (type-function-Prop A P)
is-prop-type-function-Prop A P =
  is-prop-function-type (is-prop-type-Prop P)

function-Prop :
  {l1 l2 : Level} → UU l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
pr1 (function-Prop A P) = type-function-Prop A P
pr2 (function-Prop A P) = is-prop-type-function-Prop A P

type-hom-Prop :
  { l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → UU (l1 ⊔ l2)
type-hom-Prop P Q = type-function-Prop (type-Prop P) Q

is-prop-type-hom-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  is-prop (type-hom-Prop P Q)
is-prop-type-hom-Prop P Q = is-prop-type-function-Prop (type-Prop P) Q

hom-Prop :
  { l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
pr1 (hom-Prop P Q) = type-hom-Prop P Q
pr2 (hom-Prop P Q) = is-prop-type-hom-Prop P Q

implication-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
implication-Prop P Q = hom-Prop P Q

type-implication-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (l1 ⊔ l2)
type-implication-Prop P Q = type-hom-Prop P Q
```

### The type of functions into a set is a set

```agda
abstract
  is-set-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set B → is-set (A → B)
  is-set-function-type = is-trunc-function-type zero-𝕋

type-hom-Set :
  {l1 l2 : Level} → UU-Set l1 → UU-Set l2 → UU (l1 ⊔ l2)
type-hom-Set A B = type-Set A → type-Set B

is-set-type-hom-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) →
  is-set (type-hom-Set A B)
is-set-type-hom-Set A B = is-set-function-type (is-set-type-Set B)

hom-Set :
  {l1 l2 : Level} → UU-Set l1 → UU-Set l2 → UU-Set (l1 ⊔ l2)
pr1 (hom-Set A B) = type-hom-Set A B
pr2 (hom-Set A B) = is-set-type-hom-Set A B
```

### The type of functions into a 1-type is a 1-type

```agda
abstract
  is-1-type-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-1-type B → is-1-type (A → B)
  is-1-type-function-type = is-trunc-function-type one-𝕋

type-hom-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : UU-1-Type l2) → UU (l1 ⊔ l2)
type-hom-1-Type A B = type-1-Type A → type-1-Type B

is-1-type-type-hom-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : UU-1-Type l2) →
  is-1-type (type-hom-1-Type A B)
is-1-type-type-hom-1-Type A B =
  is-1-type-function-type (is-1-type-type-1-Type B)

hom-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : UU-1-Type l2) → UU-1-Type (l1 ⊔ l2)
pr1 (hom-1-Type A B) = type-hom-1-Type A B
pr2 (hom-1-Type A B) = is-1-type-type-hom-1-Type A B
```

### The negation of a type is a proposition

```agda
is-prop-neg : {l : Level} {A : UU l} → is-prop (¬ A)
is-prop-neg {A = A} = is-prop-function-type is-prop-empty

neg-Prop' : {l1 : Level} → UU l1 → UU-Prop l1
pr1 (neg-Prop' A) = ¬ A
pr2 (neg-Prop' A) = is-prop-neg

neg-Prop : {l1 : Level} → UU-Prop l1 → UU-Prop l1
neg-Prop P = neg-Prop' (type-Prop P)

is-prop-is-empty : {l : Level} {A : UU l} → is-prop (is-empty A)
is-prop-is-empty = is-prop-neg

is-empty-Prop : {l1 : Level} → UU l1 → UU-Prop l1
pr1 (is-empty-Prop A) = is-empty A
pr2 (is-empty-Prop A) = is-prop-is-empty
```

### The double negation of a type is a proposition

```agda
dn-Prop' :
  {l : Level} (A : UU l) → UU-Prop l
dn-Prop' A = neg-Prop' (¬ A)

dn-Prop :
  {l : Level} (P : UU-Prop l) → UU-Prop l
dn-Prop P = dn-Prop' (type-Prop P)
```
