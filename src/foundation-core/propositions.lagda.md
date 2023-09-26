# Propositions

```agda
module foundation-core.propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

A type is considered to be a proposition if its identity types are contractible.
This condition is equivalent to the condition that it has up to identification
at most one element.

## Definition

```agda
is-prop : {l : Level} (A : UU l) → UU l
is-prop A = (x y : A) → is-contr (x ＝ y)

Prop :
  (l : Level) → UU (lsuc l)
Prop l = Σ (UU l) is-prop

module _
  {l : Level}
  where

  type-Prop : Prop l → UU l
  type-Prop P = pr1 P

  abstract
    is-prop-type-Prop : (P : Prop l) → is-prop (type-Prop P)
    is-prop-type-Prop P = pr2 P
```

## Examples

We prove here only that any contractible type is a proposition. The fact that
the empty type and the unit type are propositions can be found in

```text
foundation.empty-types
foundation.unit-type
```

## Properties

### To show that a type is a proposition, we may assume it is inhabited

```agda
abstract
  is-prop-is-inhabited :
    {l1 : Level} {X : UU l1} → (X → is-prop X) → is-prop X
  is-prop-is-inhabited f x y = f x x y
```

### Equivalent characterizations of propositions

```agda
module _
  {l : Level} (A : UU l)
  where

  all-elements-equal : UU l
  all-elements-equal = (x y : A) → x ＝ y

  is-proof-irrelevant : UU l
  is-proof-irrelevant = A → is-contr A

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-prop-all-elements-equal : all-elements-equal A → is-prop A
    pr1 (is-prop-all-elements-equal H x y) = (inv (H x x)) ∙ (H x y)
    pr2 (is-prop-all-elements-equal H x .x) refl = left-inv (H x x)

  abstract
    eq-is-prop' : is-prop A → all-elements-equal A
    eq-is-prop' H x y = pr1 (H x y)

  abstract
    eq-is-prop : is-prop A → {x y : A} → x ＝ y
    eq-is-prop H {x} {y} = eq-is-prop' H x y

  abstract
    is-proof-irrelevant-all-elements-equal :
      all-elements-equal A → is-proof-irrelevant A
    pr1 (is-proof-irrelevant-all-elements-equal H a) = a
    pr2 (is-proof-irrelevant-all-elements-equal H a) = H a

  abstract
    is-proof-irrelevant-is-prop : is-prop A → is-proof-irrelevant A
    is-proof-irrelevant-is-prop =
      is-proof-irrelevant-all-elements-equal ∘ eq-is-prop'

  abstract
    is-prop-is-proof-irrelevant : is-proof-irrelevant A → is-prop A
    is-prop-is-proof-irrelevant H x y = is-prop-is-contr (H x) x y

  abstract
    eq-is-proof-irrelevant : is-proof-irrelevant A → all-elements-equal A
    eq-is-proof-irrelevant = eq-is-prop' ∘ is-prop-is-proof-irrelevant
```

### A map between propositions is an equivalence if there is a map in the reverse direction

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-is-prop :
      is-prop A → is-prop B → {f : A → B} → (B → A) → is-equiv f
    is-equiv-is-prop is-prop-A is-prop-B {f} g =
      is-equiv-is-invertible
        ( g)
        ( λ y → eq-is-prop is-prop-B)
        ( λ x → eq-is-prop is-prop-A)

  abstract
    equiv-prop : is-prop A → is-prop B → (A → B) → (B → A) → A ≃ B
    pr1 (equiv-prop is-prop-A is-prop-B f g) = f
    pr2 (equiv-prop is-prop-A is-prop-B f g) =
      is-equiv-is-prop is-prop-A is-prop-B g
```

### Propositions are closed under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-is-equiv : {f : A → B} → is-equiv f → is-prop B → is-prop A
    is-prop-is-equiv {f} E H =
      is-prop-is-proof-irrelevant
        ( λ a → is-contr-is-equiv B f E (is-proof-irrelevant-is-prop H (f a)))

  abstract
    is-prop-equiv : A ≃ B → is-prop B → is-prop A
    is-prop-equiv (pair f is-equiv-f) = is-prop-is-equiv is-equiv-f

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-is-equiv' : {f : A → B} → is-equiv f → is-prop A → is-prop B
    is-prop-is-equiv' E H =
      is-prop-is-equiv (is-equiv-map-inv-is-equiv E) H

  abstract
    is-prop-equiv' : A ≃ B → is-prop A → is-prop B
    is-prop-equiv' (pair f is-equiv-f) = is-prop-is-equiv' is-equiv-f
```

### Propositions are closed under dependent pair types

```agda
abstract
  is-prop-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-prop A → ((x : A) → is-prop (B x)) → is-prop (Σ A B)
  is-prop-Σ H K x y =
    is-contr-equiv'
      ( Eq-Σ x y)
      ( equiv-eq-pair-Σ x y)
      ( is-contr-Σ'
        ( H (pr1 x) (pr1 y))
        ( λ p → K (pr1 y) (tr _ p (pr2 x)) (pr2 y)))

Σ-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : type-Prop P → Prop l2) →
  Prop (l1 ⊔ l2)
pr1 (Σ-Prop P Q) = Σ (type-Prop P) (λ p → type-Prop (Q p))
pr2 (Σ-Prop P Q) =
  is-prop-Σ
    ( is-prop-type-Prop P)
    ( λ p → is-prop-type-Prop (Q p))
```

### Propositions are closed under cartesian product types

```agda
abstract
  is-prop-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop A → is-prop B → is-prop (A × B)
  is-prop-prod H K = is-prop-Σ H (λ x → K)

prod-Prop : {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
pr1 (prod-Prop P Q) = type-Prop P × type-Prop Q
pr2 (prod-Prop P Q) = is-prop-prod (is-prop-type-Prop P) (is-prop-type-Prop Q)
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
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2) → UU (l1 ⊔ l2)
type-Π-Prop A P = (x : A) → type-Prop (P x)

is-prop-type-Π-Prop :
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2) → is-prop (type-Π-Prop A P)
is-prop-type-Π-Prop A P = is-prop-Π (λ x → is-prop-type-Prop (P x))

Π-Prop :
  {l1 l2 : Level} (A : UU l1) →
  (A → Prop l2) → Prop (l1 ⊔ l2)
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
        ( is-equiv-is-invertible
          ( λ g {x} → g x)
          ( refl-htpy)
          ( refl-htpy)))
      ( is-prop-Π H)

type-Π-Prop' :
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2) → UU (l1 ⊔ l2)
type-Π-Prop' A P = {x : A} → type-Prop (P x)

is-prop-type-Π-Prop' :
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2) → is-prop (type-Π-Prop' A P)
is-prop-type-Π-Prop' A P = is-prop-Π' (λ x → is-prop-type-Prop (P x))

Π-Prop' : {l1 l2 : Level} (A : UU l1) (P : A → Prop l2) → Prop (l1 ⊔ l2)
pr1 (Π-Prop' A P) = type-Π-Prop' A P
pr2 (Π-Prop' A P) = is-prop-Π' (λ x → is-prop-type-Prop (P x))
```

For convenience, we also record repeated applications of the above.

#### Higher order products of families of propositions are propositions

```agda
is-prop-Π² :
  {l1 l2 l3 : Level}
  {A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) (x2 : A2 x1) → UU l3} →
  ((x1 : A1) (x2 : A2 x1) → is-prop (A3 x1 x2)) →
  is-prop ((x1 : A1) (x2 : A2 x1) → A3 x1 x2)
is-prop-Π² H = is-prop-Π (is-prop-Π ∘ H)

is-prop-Π³ :
  {l1 l2 l3 l4 : Level}
  {A1 : UU l1}
  {A2 : A1 → UU l2}
  {A3 : (x1 : A1) (x2 : A2 x1) → UU l3}
  {A4 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) → UU l4} →
  ((x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) → is-prop (A4 x1 x2 x3)) →
  is-prop ((x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) → A4 x1 x2 x3)
is-prop-Π³ H = is-prop-Π (is-prop-Π² ∘ H)

is-prop-Π⁴ :
  {l1 l2 l3 l4 l5 : Level}
  {A1 : UU l1}
  {A2 : A1 → UU l2}
  {A3 : (x1 : A1) (x2 : A2 x1) → UU l3}
  {A4 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) → UU l4}
  {A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5} →
  ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) →
    is-prop (A5 x1 x2 x3 x4)) →
  is-prop
    ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) →
      A5 x1 x2 x3 x4)
is-prop-Π⁴ H = is-prop-Π (is-prop-Π³ ∘ H)

is-prop-Π⁵ :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A1 : UU l1}
  {A2 : A1 → UU l2}
  {A3 : (x1 : A1) (x2 : A2 x1) → UU l3}
  {A4 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) → UU l4}
  {A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5} →
  {A6 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) →
    UU l6} →
  ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) →
    is-prop (A6 x1 x2 x3 x4 x5)) →
  is-prop
    ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) →
      A6 x1 x2 x3 x4 x5)
is-prop-Π⁵ H = is-prop-Π (is-prop-Π⁴ ∘ H)

is-prop-Π⁶ :
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A1 : UU l1}
  {A2 : A1 → UU l2}
  {A3 : (x1 : A1) (x2 : A2 x1) → UU l3}
  {A4 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) → UU l4}
  {A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5} →
  {A6 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) → UU l6} →
  {A7 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7} →
  ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) →
    is-prop (A7 x1 x2 x3 x4 x5 x6)) →
  is-prop
    ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) →
      A7 x1 x2 x3 x4 x5 x6)
is-prop-Π⁶ H = is-prop-Π (is-prop-Π⁵ ∘ H)

is-prop-Π⁷ :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A1 : UU l1}
  {A2 : A1 → UU l2}
  {A3 : (x1 : A1) (x2 : A2 x1) → UU l3}
  {A4 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) → UU l4}
  {A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5} →
  {A6 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) → UU l6} →
  {A7 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7} →
  {A8 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8} →
  ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) →
    is-prop (A8 x1 x2 x3 x4 x5 x6 x7)) →
  is-prop
    ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) →
      A8 x1 x2 x3 x4 x5 x6 x7)
is-prop-Π⁷ H = is-prop-Π (is-prop-Π⁶ ∘ H)

is-prop-Π⁸ :
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A1 : UU l1}
  {A2 : A1 → UU l2}
  {A3 : (x1 : A1) (x2 : A2 x1) → UU l3}
  {A4 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) → UU l4}
  {A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
  {A6 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) → UU l6} →
  {A7 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
  {A8 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
  {A9 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) → UU l9} →
  ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) →
    is-prop (A9 x1 x2 x3 x4 x5 x6 x7 x8)) →
  is-prop
    ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) →
      A9 x1 x2 x3 x4 x5 x6 x7 x8)
is-prop-Π⁸ H = is-prop-Π (is-prop-Π⁷ ∘ H)

is-prop-Π⁹ :
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 : Level}
  {A1 : UU l1}
  {A2 : A1 → UU l2}
  {A3 : (x1 : A1) (x2 : A2 x1) → UU l3}
  {A4 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) → UU l4}
  {A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
  {A6 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) → UU l6} →
  {A7 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
  {A8 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
  {A9 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) → UU l9} →
  {A10 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
    (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) → UU l10} →
  ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
    (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) →
    is-prop (A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)) →
  is-prop
    ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) →
      A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
is-prop-Π⁹ H = is-prop-Π (is-prop-Π⁸ ∘ H)

is-prop-Π¹⁰ :
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 : Level}
  {A1 : UU l1}
  {A2 : A1 → UU l2}
  {A3 : (x1 : A1) (x2 : A2 x1) → UU l3}
  {A4 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) → UU l4}
  {A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
  {A6 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) → UU l6} →
  {A7 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
  {A8 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
  {A9 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) → UU l9} →
  {A10 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
    (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) → UU l10}
  {A11 :
    (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
    (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9) →
    UU l11} →
  ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
    (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
    (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
    (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9) →
    is-prop (A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) →
  is-prop
    ( (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9) →
      A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
is-prop-Π¹⁰ H = is-prop-Π (is-prop-Π⁹ ∘ H)
```

### The type of functions into a proposition is a proposition

```agda
abstract
  is-prop-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop B → is-prop (A → B)
  is-prop-function-type H = is-prop-Π (λ _ → H)

type-function-Prop :
  {l1 l2 : Level} → UU l1 → Prop l2 → UU (l1 ⊔ l2)
type-function-Prop A P = A → type-Prop P

is-prop-type-function-Prop :
  {l1 l2 : Level} (A : UU l1) (P : Prop l2) →
  is-prop (type-function-Prop A P)
is-prop-type-function-Prop A P =
  is-prop-function-type (is-prop-type-Prop P)

function-Prop :
  {l1 l2 : Level} → UU l1 → Prop l2 → Prop (l1 ⊔ l2)
pr1 (function-Prop A P) = type-function-Prop A P
pr2 (function-Prop A P) = is-prop-type-function-Prop A P

type-hom-Prop :
  { l1 l2 : Level} (P : Prop l1) (Q : Prop l2) → UU (l1 ⊔ l2)
type-hom-Prop P Q = type-function-Prop (type-Prop P) Q

is-prop-type-hom-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  is-prop (type-hom-Prop P Q)
is-prop-type-hom-Prop P Q = is-prop-type-function-Prop (type-Prop P) Q

hom-Prop :
  { l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
pr1 (hom-Prop P Q) = type-hom-Prop P Q
pr2 (hom-Prop P Q) = is-prop-type-hom-Prop P Q

implication-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
implication-Prop P Q = hom-Prop P Q

type-implication-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → UU (l1 ⊔ l2)
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
  { l1 l2 : Level} (P : Prop l1) (Q : Prop l2) → UU (l1 ⊔ l2)
type-equiv-Prop P Q = (type-Prop P) ≃ (type-Prop Q)

abstract
  is-prop-type-equiv-Prop :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-prop (type-equiv-Prop P Q)
  is-prop-type-equiv-Prop P Q =
    is-prop-equiv-is-prop (is-prop-type-Prop P) (is-prop-type-Prop Q)

equiv-Prop :
  { l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
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
  is-prop-is-prop A = is-prop-Π (λ x → is-prop-Π (λ y → is-property-is-contr))

is-prop-Prop : {l : Level} (A : UU l) → Prop l
pr1 (is-prop-Prop A) = is-prop A
pr2 (is-prop-Prop A) = is-prop-is-prop A
```
