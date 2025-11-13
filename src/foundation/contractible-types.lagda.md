# Contractible types

```agda
module foundation.contractible-types where

open import foundation-core.contractible-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.function-extensionality
open import foundation.logical-equivalences
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Definition

### The proposition of being contractible

```agda
is-contr-Prop : {l : Level} → UU l → Prop l
pr1 (is-contr-Prop A) = is-contr A
pr2 (is-contr-Prop A) = is-property-is-contr
```

### The subuniverse of contractible types

```agda
Contr : (l : Level) → UU (lsuc l)
Contr l = type-subuniverse is-contr-Prop

type-Contr : {l : Level} → Contr l → UU l
type-Contr A = pr1 A

abstract
  is-contr-type-Contr :
    {l : Level} (A : Contr l) → is-contr (type-Contr A)
  is-contr-type-Contr A = pr2 A

equiv-Contr :
  {l1 l2 : Level} (X : Contr l1) (Y : Contr l2) → UU (l1 ⊔ l2)
equiv-Contr X Y = type-Contr X ≃ type-Contr Y

equiv-eq-Contr :
  {l1 : Level} (X Y : Contr l1) → X ＝ Y → equiv-Contr X Y
equiv-eq-Contr X Y = equiv-eq-subuniverse is-contr-Prop X Y

abstract
  is-equiv-equiv-eq-Contr :
    {l1 : Level} (X Y : Contr l1) → is-equiv (equiv-eq-Contr X Y)
  is-equiv-equiv-eq-Contr X Y =
    is-equiv-equiv-eq-subuniverse is-contr-Prop X Y

eq-equiv-Contr :
  {l1 : Level} {X Y : Contr l1} → equiv-Contr X Y → X ＝ Y
eq-equiv-Contr = eq-equiv-subuniverse is-contr-Prop

abstract
  center-Contr : (l : Level) → Contr l
  center-Contr l = pair (raise-unit l) is-contr-raise-unit

  contraction-Contr :
    {l : Level} (A : Contr l) → center-Contr l ＝ A
  contraction-Contr A =
    eq-equiv-Contr
      ( equiv-is-contr is-contr-raise-unit (is-contr-type-Contr A))

abstract
  is-contr-Contr : (l : Level) → is-contr (Contr l)
  is-contr-Contr l = pair (center-Contr l) contraction-Contr
```

### The predicate that a subuniverse contains any contractible types

```agda
contains-contractible-types-subuniverse :
  {l1 l2 : Level} → subuniverse l1 l2 → UU (lsuc l1 ⊔ l2)
contains-contractible-types-subuniverse {l1} P =
  (X : UU l1) → is-contr X → is-in-subuniverse P X
```

### The predicate that a subuniverse is closed under the `is-contr` predicate

We state a general form involving two universes, and a more traditional form
using a single universe

```agda
is-closed-under-is-contr-subuniverses :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (Q : subuniverse l1 l3) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
is-closed-under-is-contr-subuniverses P Q =
  (X : type-subuniverse P) →
  is-in-subuniverse Q (is-contr (inclusion-subuniverse P X))

is-closed-under-is-contr-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU (lsuc l1 ⊔ l2)
is-closed-under-is-contr-subuniverse P =
  is-closed-under-is-contr-subuniverses P P
```

## Properties

### If two types are equivalent then so are the propositions that they are contractible

```agda
equiv-is-contr-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A ≃ B → is-contr A ≃ is-contr B
equiv-is-contr-equiv {A = A} {B = B} e =
  equiv-iff-is-prop
    ( is-property-is-contr)
    ( is-property-is-contr)
    ( is-contr-retract-of A
      ( map-inv-equiv e , map-equiv e , is-section-map-inv-equiv e))
    ( is-contr-retract-of B
      ( map-equiv e , map-inv-equiv e , is-retraction-map-inv-equiv e))
```

### Contractible types are `k`-truncated for any `k`

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-trunc-is-contr : (k : 𝕋) → is-contr A → is-trunc k A
    is-trunc-is-contr neg-two-𝕋 is-contr-A = is-contr-A
    is-trunc-is-contr (succ-𝕋 k) is-contr-A =
      is-trunc-succ-is-trunc k (is-trunc-is-contr k is-contr-A)
```

### Contractibility of Σ-types where the dependent type is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

  is-contr-Σ-is-prop :
    ((x : A) → is-prop (B x)) → ((x : A) → B x → a ＝ x) → is-contr (Σ A B)
  pr1 (is-contr-Σ-is-prop p f) = a , b
  pr2 (is-contr-Σ-is-prop p f) (x , y) =
    eq-type-subtype (λ x' → B x' , p x') (f x y)
```

### The diagonal of contractible types

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  abstract
    is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponential :
      ({l : Level} (X : UU l) → is-equiv (diagonal-exponential X A)) →
      is-equiv (diagonal-exponential A A)
    is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponential H = H A

  abstract
    is-contr-is-equiv-self-diagonal-exponential :
      is-equiv (diagonal-exponential A A) → is-contr A
    is-contr-is-equiv-self-diagonal-exponential H =
      tot (λ x → htpy-eq) (center (is-contr-map-is-equiv H id))

  abstract
    is-contr-is-equiv-diagonal-exponential :
      ({l : Level} (X : UU l) → is-equiv (diagonal-exponential X A)) →
      is-contr A
    is-contr-is-equiv-diagonal-exponential H =
      is-contr-is-equiv-self-diagonal-exponential
        ( is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponential H)

  abstract
    is-equiv-diagonal-exponential-is-contr :
      is-contr A →
      {l : Level} (X : UU l) → is-equiv (diagonal-exponential X A)
    is-equiv-diagonal-exponential-is-contr H X =
      is-equiv-is-invertible
        ( ev-point' (center H))
        ( λ f → eq-htpy (λ x → ap f (contraction H x)))
        ( refl-htpy)

  equiv-diagonal-exponential-is-contr :
    {l : Level} (X : UU l) → is-contr A → X ≃ (A → X)
  pr1 (equiv-diagonal-exponential-is-contr X H) =
    diagonal-exponential X A
  pr2 (equiv-diagonal-exponential-is-contr X H) =
    is-equiv-diagonal-exponential-is-contr H X

  abstract
    is-equiv-diagonal-exponential-is-contr' :
      is-contr A →
      {l : Level} (X : UU l) → is-equiv (diagonal-exponential A X)
    is-equiv-diagonal-exponential-is-contr' H X =
      is-equiv-is-invertible
        ( λ _ → center H)
        ( λ x → eq-htpy (contraction H ∘ x))
        ( contraction H)

  equiv-diagonal-exponential-is-contr' :
    {l : Level} (X : UU l) → is-contr A → A ≃ (X → A)
  equiv-diagonal-exponential-is-contr' X H =
    ( diagonal-exponential A X , is-equiv-diagonal-exponential-is-contr' H X)

  abstract
    is-contr-is-equiv-diagonal-exponential' :
      ({l : Level} (X : UU l) → is-equiv (diagonal-exponential A X)) →
      is-contr A
    is-contr-is-equiv-diagonal-exponential' H =
      is-contr-is-equiv-self-diagonal-exponential (H A)
```
