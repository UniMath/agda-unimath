# Contractible types

```agda
module foundation.contractible-types where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.contractible-types public

open import foundation.function-extensionality
open import foundation.subuniverses
open import foundation.unit-type

open import foundation-core.constant-maps
open import foundation-core.contractible-maps
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.singleton-induction
open import foundation-core.subtypes
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.universe-levels
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
  {l1 : Level} (X Y : Contr l1) → (X ＝ Y) → equiv-Contr X Y
equiv-eq-Contr X Y = equiv-eq-subuniverse is-contr-Prop X Y

abstract
  is-equiv-equiv-eq-Contr :
    {l1 : Level} (X Y : Contr l1) → is-equiv (equiv-eq-Contr X Y)
  is-equiv-equiv-eq-Contr X Y =
    is-equiv-equiv-eq-subuniverse is-contr-Prop X Y

eq-equiv-Contr :
  {l1 : Level} {X Y : Contr l1} → equiv-Contr X Y → (X ＝ Y)
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

## Properties

### If two types are equivalent then so are the propositions that they are contractible

```agda
equiv-is-contr-equiv : {l1 l2 : Level} {A : UU l1} {B : UU l2}
  → A ≃ B → is-contr A ≃ is-contr B
equiv-is-contr-equiv {A = A} {B = B} e =
  equiv-prop
    ( is-property-is-contr)
    ( is-property-is-contr)
    ( is-contr-retract-of A (pair (map-inv-equiv e) (pair (map-equiv e) (issec-map-inv-equiv e))))
    ( is-contr-retract-of B (pair (map-equiv e) (pair (map-inv-equiv e) (isretr-map-inv-equiv e))))
```

### Contractible types are k-truncated for any k.

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
module _ {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a) where

  is-contr-Σ-is-prop :
    ((x : A) → is-prop (B x)) → ((x : A) → B x → a ＝ x) → is-contr (Σ A B)
  pr1 (is-contr-Σ-is-prop p f) = pair a b
  pr2 (is-contr-Σ-is-prop p f) (pair x y) =
    eq-type-subtype
      ( λ x' → pair (B x') (p x'))
      ( f x y)
```

### Equivalent characterizations of contractible types

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  ev-point : {l2 : Level} (a : A) {P : A → UU l2} → ((x : A) → P x) → P a
  ev-point a f = f a

  ev-point' : {l2 : Level} (a : A) {X : UU l2} → (A → X) → X
  ev-point' a f = f a

  dependent-universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  dependent-universal-property-contr l a =
    (P : A → UU l) → is-equiv (ev-point a {P})

  universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  universal-property-contr l a =
    (X : UU l) → is-equiv (ev-point' a {X})

  universal-property-dependent-universal-property-contr :
    (a : A) →
    ({l : Level} → dependent-universal-property-contr l a) →
    ({l : Level} → universal-property-contr l a)
  universal-property-dependent-universal-property-contr a dup-contr {l} X =
    dup-contr {l} (λ x → X)

  abstract
    is-equiv-ev-point-universal-property-contr :
      (a : A) → ({l : Level} → universal-property-contr l a) →
      is-equiv (ev-point' a {A})
    is-equiv-ev-point-universal-property-contr a up-contr =
      up-contr A

  abstract
    is-contr-is-equiv-ev-point :
      (a : A) → is-equiv (ev-point' a {X = A}) → is-contr A
    pr1 (is-contr-is-equiv-ev-point a H) = a
    pr2 (is-contr-is-equiv-ev-point a H) =
      htpy-eq
        ( ap
          ( pr1)
          ( eq-is-contr'
            ( is-contr-map-is-equiv H a)
            ( pair (λ x → a) refl)
            ( pair id refl)))

  abstract
    is-contr-universal-property-contr :
      (a : A) →
      ({l : Level} → universal-property-contr l a) → is-contr A
    is-contr-universal-property-contr a up-contr =
      is-contr-is-equiv-ev-point a
        ( is-equiv-ev-point-universal-property-contr a up-contr)

  abstract
    is-contr-dependent-universal-property-contr :
      (a : A) →
      ({l : Level} → dependent-universal-property-contr l a) → is-contr A
    is-contr-dependent-universal-property-contr a dup-contr =
      is-contr-universal-property-contr a
        ( universal-property-dependent-universal-property-contr a dup-contr)

  abstract
    dependent-universal-property-contr-is-contr :
      (a : A) → is-contr A →
      {l : Level} → dependent-universal-property-contr l a
    dependent-universal-property-contr-is-contr a H {l} P =
      is-equiv-has-inverse
        ( ind-singleton-is-contr a H P)
        ( comp-singleton-is-contr a H P)
        ( λ f →
          eq-htpy
            ( ind-singleton-is-contr a H
              ( λ x → ind-singleton-is-contr a H P (f a) x ＝ f x)
              ( comp-singleton-is-contr a H P (f a))))

  equiv-dependent-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (B : A → UU l) → ((x : A) → B x) ≃ B a
  pr1 (equiv-dependent-universal-property-contr a H P) = ev-point a
  pr2 (equiv-dependent-universal-property-contr a H P) =
    dependent-universal-property-contr-is-contr a H P

  abstract
    universal-property-contr-is-contr :
      (a : A) → is-contr A → {l : Level} → universal-property-contr l a
    universal-property-contr-is-contr a H =
      universal-property-dependent-universal-property-contr a
        ( dependent-universal-property-contr-is-contr a H)

  equiv-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (X : UU l) → (A → X) ≃ X
  pr1 (equiv-universal-property-contr a H X) = ev-point' a
  pr2 (equiv-universal-property-contr a H X) =
    universal-property-contr-is-contr a H X

  abstract
    is-equiv-self-diagonal-is-equiv-diagonal :
      ({l : Level} (X : UU l) → is-equiv (λ x → const A X x)) →
      is-equiv (λ x → const A A x)
    is-equiv-self-diagonal-is-equiv-diagonal H = H A

  abstract
    is-contr-is-equiv-self-diagonal :
      is-equiv (λ x → const A A x) → is-contr A
    is-contr-is-equiv-self-diagonal H =
      tot (λ x → htpy-eq) (center (is-contr-map-is-equiv H id))

  abstract
    is-contr-is-equiv-diagonal :
      ({l : Level} (X : UU l) → is-equiv (λ x → const A X x)) → is-contr A
    is-contr-is-equiv-diagonal H =
      is-contr-is-equiv-self-diagonal
        ( is-equiv-self-diagonal-is-equiv-diagonal H)

  abstract
    is-equiv-diagonal-is-contr :
      is-contr A →
      {l : Level} (X : UU l) → is-equiv (λ x → const A X x)
    is-equiv-diagonal-is-contr H X =
      is-equiv-has-inverse
        ( ev-point' (center H))
        ( λ f → eq-htpy (λ x → ap f (contraction H x)))
        ( λ x → refl)

  equiv-diagonal-is-contr :
    {l : Level} (X : UU l) → is-contr A → X ≃ (A → X)
  pr1 (equiv-diagonal-is-contr X H) = const A X
  pr2 (equiv-diagonal-is-contr X H) = is-equiv-diagonal-is-contr H X
```
