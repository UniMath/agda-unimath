# Sets

```agda
module foundation-core.sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A type is a {{#concept "set" Agda=is-set}} if its
[identity types](foundation-core.identity-types.md) are
[propositions](foundation-core.propositions.md).

## Definition

```agda
is-set : {l : Level} → UU l → UU l
is-set A = (x y : A) → is-prop (x ＝ y)

Set : (l : Level) → UU (lsuc l)
Set l = Σ (UU l) is-set

module _
  {l : Level} (X : Set l)
  where

  type-Set : UU l
  type-Set = pr1 X

  abstract
    is-set-type-Set : is-set type-Set
    is-set-type-Set = pr2 X

  Id-Prop : (x y : type-Set) → Prop l
  Id-Prop x y = (x ＝ y , is-set-type-Set x y)
```

## Properties

### A type is a set if and only if it satisfies Streicher's axiom K

```agda
instance-axiom-K : {l : Level} → UU l → UU l
instance-axiom-K A = (x : A) (p : x ＝ x) → refl ＝ p

axiom-K-Level : (l : Level) → UU (lsuc l)
axiom-K-Level l = (A : UU l) → instance-axiom-K A

axiom-K : UUω
axiom-K = {l : Level} → axiom-K-Level l

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-set-axiom-K' :
      instance-axiom-K A → (x y : A) → all-elements-equal (x ＝ y)
    is-set-axiom-K' K x .x refl q with K x q
    ... | refl = refl

  abstract
    is-set-axiom-K : instance-axiom-K A → is-set A
    is-set-axiom-K H x y = is-prop-all-elements-equal (is-set-axiom-K' H x y)

  abstract
    axiom-K-is-set : is-set A → instance-axiom-K A
    axiom-K-is-set H x p =
      ( inv (contraction (is-proof-irrelevant-is-prop (H x x) refl) refl)) ∙
      ( contraction (is-proof-irrelevant-is-prop (H x x) refl) p)
```

### A type is a set if and only if it satisfies uniqueness of identity proofs

A type `A` is said to satisfy
{{#concept "uniqueness of identity proofs" Agda=has-uip}} if for all elements
`x y : A` all equality proofs `x ＝ y` are equal.

```agda
has-uip : {l : Level} → UU l → UU l
has-uip A = (x y : A) → all-elements-equal (x ＝ y)

module _
  {l : Level} {A : UU l}
  where

  is-set-has-uip : is-set A → has-uip A
  is-set-has-uip is-set-A x y = eq-is-prop' (is-set-A x y)

  has-uip-is-set : has-uip A → is-set A
  has-uip-is-set uip-A x y = is-prop-all-elements-equal (uip-A x y)
```

### If a reflexive binary relation maps into the identity type of `A`, then `A` is a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} (x : A) (R : A → UU l2)
  (p : (y : A) → is-prop (R y)) (ρ : R x)
  (i : (y : A) → R y → x ＝ y)
  where

  abstract
    is-equiv-prop-in-based-id : (y : A) → is-equiv (i y)
    is-equiv-prop-in-based-id =
      fundamental-theorem-id-retraction x i
        ( λ y → (ind-Id x (λ z p → R z) ρ y) , (λ r → eq-is-prop (p y)))

  abstract
    is-torsorial-prop-in-based-id : is-torsorial R
    is-torsorial-prop-in-based-id =
      fundamental-theorem-id'
        ( λ y → map-inv-is-equiv (is-equiv-prop-in-based-id y))
        ( λ y → is-equiv-map-inv-is-equiv (is-equiv-prop-in-based-id y))

  abstract
    is-prop-based-Id-prop-in-based-id : (y : A) → is-prop (x ＝ y)
    is-prop-based-Id-prop-in-based-id y =
      is-prop-is-equiv' (is-equiv-prop-in-based-id y) (p y)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : A → A → UU l2)
  (p : (x y : A) → is-prop (R x y)) (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → x ＝ y)
  where

  abstract
    is-equiv-prop-in-id : (x y : A) → is-equiv (i x y)
    is-equiv-prop-in-id x = is-equiv-prop-in-based-id x (R x) (p x) (ρ x) (i x)

  abstract
    is-set-prop-in-id : is-set A
    is-set-prop-in-id x =
      is-prop-based-Id-prop-in-based-id x (R x) (p x) (ρ x) (i x)
```

### Any proposition is a set

```agda
abstract
  is-set-is-prop :
    {l : Level} {P : UU l} → is-prop P → is-set P
  is-set-is-prop = is-trunc-succ-is-trunc neg-one-𝕋

set-Prop :
  {l : Level} → Prop l → Set l
set-Prop P = truncated-type-succ-Truncated-Type neg-one-𝕋 P
```

### Sets are closed under equivalences

```agda
abstract
  is-set-is-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) (f : A → B) → is-equiv f →
    is-set B → is-set A
  is-set-is-equiv = is-trunc-is-equiv zero-𝕋

abstract
  is-set-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) (e : A ≃ B) →
    is-set B → is-set A
  is-set-equiv = is-trunc-equiv zero-𝕋

abstract
  is-set-is-equiv' :
    {l1 l2 : Level} (A : UU l1) {B : UU l2} (f : A → B) → is-equiv f →
    is-set A → is-set B
  is-set-is-equiv' = is-trunc-is-equiv' zero-𝕋

abstract
  is-set-equiv' :
    {l1 l2 : Level} (A : UU l1) {B : UU l2} (e : A ≃ B) →
    is-set A → is-set B
  is-set-equiv' = is-trunc-equiv' zero-𝕋

abstract
  is-set-equiv-is-set :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A ≃ B)
  is-set-equiv-is-set = is-trunc-equiv-is-trunc zero-𝕋

module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  where

  equiv-Set : UU (l1 ⊔ l2)
  equiv-Set = type-Set A ≃ type-Set B

  equiv-set-Set : Set (l1 ⊔ l2)
  pr1 equiv-set-Set = equiv-Set
  pr2 equiv-set-Set =
    is-set-equiv-is-set (is-set-type-Set A) (is-set-type-Set B)
```

### If a type injects into a set, then it is a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-set-is-injective :
      {f : A → B} → is-set B → is-injective f → is-set A
    is-set-is-injective {f} H I =
      is-set-prop-in-id
        ( λ x y → f x ＝ f y)
        ( λ x y → H (f x) (f y))
        ( λ x → refl)
        ( λ x y → I)
```
