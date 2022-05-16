# Propositions

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.propositions where

open import foundation-core.propositions public

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using (is-equiv-has-inverse; _≃_)
open import foundation-core.function-extensionality using
  ( htpy-eq; equiv-funext)
open import foundation-core.functions using (id; _∘_)
open import foundation-core.homotopies using (_~_; refl-htpy)
open import foundation-core.truncated-types using
  ( is-trunc)
open import foundation-core.truncation-levels using
  ( 𝕋; neg-two-𝕋; neg-one-𝕋; succ-𝕋)
open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.contractible-types using
  ( is-contr; is-trunc-is-contr; eq-is-contr; is-contr-equiv; is-contr-Π;
    is-prop-is-contr; is-subtype-is-contr)
```

### Propositions are (k+1)-truncated for any k.

```agda
abstract
  is-trunc-is-prop :
    { l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
  is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)
```

### Products of families of propositions are propositions

```agda
abstract
  is-prop-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-prop (B x)) → is-prop ((x : A) → B x)
  is-prop-Π H =
    is-prop-is-proof-irrelevant
      ( λ f → is-contr-Π (λ x → is-proof-irrelevant-is-prop (H x) (f x)))

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
    ((x : A) → is-prop (B x)) → is-prop ({x : A} → B x)
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

### The type of functions into a proposition is a proposition

```agda
abstract
  is-prop-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop B → is-prop (A → B)
  is-prop-function-type H = is-prop-Π (λ x → H)

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

### The type of equivalences between two propositions is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-equiv-is-prop : is-prop A → is-prop B → is-prop (A ≃ B)
  is-prop-equiv-is-prop H K =
    is-prop-Σ
      ( is-prop-function-type K)
      ( λ f →
        is-prop-prod
          ( is-prop-Σ
            ( is-prop-function-type H)
            ( λ g → is-prop-is-contr (is-contr-Π (λ y → K (f (g y)) y))))
          ( is-prop-Σ
            ( is-prop-function-type H)
            ( λ h → is-prop-is-contr (is-contr-Π (λ x → H (h (f x)) x)))))

type-equiv-Prop :
  { l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → UU (l1 ⊔ l2)
type-equiv-Prop P Q = (type-Prop P) ≃ (type-Prop Q)

abstract
  is-prop-type-equiv-Prop :
    {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
    is-prop (type-equiv-Prop P Q)
  is-prop-type-equiv-Prop P Q =
    is-prop-equiv-is-prop (is-prop-type-Prop P) (is-prop-type-Prop Q)

equiv-Prop :
  { l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
pr1 (equiv-Prop P Q) = type-equiv-Prop P Q
pr2 (equiv-Prop P Q) = is-prop-type-equiv-Prop P Q
```

### A type is a proposition if and only if the type of its endomaps is contractible

```agda
abstract
  is-prop-is-contr-endomaps :
    {l : Level} (P : UU l) → is-contr (P → P) → is-prop P
  is-prop-is-contr-endomaps P H =
    is-prop-all-elements-equal (λ x → htpy-eq (eq-is-contr H))

abstract
  is-contr-endomaps-is-prop :
    {l : Level} (P : UU l) → is-prop P → is-contr (P → P)
  is-contr-endomaps-is-prop P is-prop-P =
    is-proof-irrelevant-is-prop (is-prop-function-type is-prop-P) id
```

### Being a proposition is a proposition

```agda
abstract
  is-prop-is-prop :
    {l : Level} (A : UU l) → is-prop (is-prop A)
  is-prop-is-prop A = is-prop-Π (λ x → is-prop-Π (λ y → is-subtype-is-contr))

is-prop-Prop : {l : Level} (A : UU l) → UU-Prop l
pr1 (is-prop-Prop A) = is-prop A
pr2 (is-prop-Prop A) = is-prop-is-prop A
```
