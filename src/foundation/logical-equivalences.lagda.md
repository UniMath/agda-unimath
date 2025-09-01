# Logical equivalences

```agda
module foundation.logical-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalence-extensionality
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

{{#concept "Logical equivalences" Disambiguation="of types" Agda=iff}} between
two types `A` and `B` consist of a map `A → B` and a map `B → A`. The type of
logical equivalences between types is the
[Curry–Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of logical equivalences between [propositions](foundation-core.propositions.md).

## Definition

### The structure on a map of being a logical equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-converse : (A → B) → UU (l1 ⊔ l2)
  has-converse f = B → A

  is-prop-has-converse :
    is-prop A → (f : A → B) → is-prop (has-converse f)
  is-prop-has-converse is-prop-A f = is-prop-function-type is-prop-A

has-converse-Prop :
  {l1 l2 : Level} (A : Prop l1) {B : UU l2} → (type-Prop A → B) → Prop (l1 ⊔ l2)
has-converse-Prop A f =
  ( has-converse f ,
    is-prop-has-converse (is-prop-type-Prop A) f)
```

### Logical equivalences between types

```agda
iff : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
iff A B = Σ (A → B) has-converse

infix 6 _↔_

_↔_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
_↔_ = iff

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : A ↔ B)
  where

  forward-implication : A → B
  forward-implication = pr1 H

  backward-implication : B → A
  backward-implication = pr2 H
```

### Logical equivalences between propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  type-iff-Prop : UU (l1 ⊔ l2)
  type-iff-Prop = type-Prop P ↔ type-Prop Q

  is-prop-iff-Prop : is-prop type-iff-Prop
  is-prop-iff-Prop =
    is-prop-product
      ( is-prop-function-type (is-prop-type-Prop Q))
      ( is-prop-function-type (is-prop-type-Prop P))

  iff-Prop : Prop (l1 ⊔ l2)
  pr1 iff-Prop = type-iff-Prop
  pr2 iff-Prop = is-prop-iff-Prop

  infix 6 _⇔_

  _⇔_ : Prop (l1 ⊔ l2)
  _⇔_ = iff-Prop
```

### The identity logical equivalence

```agda
id-iff : {l1 : Level} {A : UU l1} → A ↔ A
id-iff = (id , id)
```

### Composition of logical equivalences

```agda
infixr 15 _∘iff_

_∘iff_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (B ↔ C) → (A ↔ B) → (A ↔ C)
pr1 ((g1 , g2) ∘iff (f1 , f2)) = g1 ∘ f1
pr2 ((g1 , g2) ∘iff (f1 , f2)) = f2 ∘ g2
```

### Inverting a logical equivalence

```agda
inv-iff :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A ↔ B) → (B ↔ A)
pr1 (inv-iff (f , g)) = g
pr2 (inv-iff (f , g)) = f
```

## Properties

### Characterizing equality of logical equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  htpy-iff : (f g : A ↔ B) → UU (l1 ⊔ l2)
  htpy-iff f g =
    ( forward-implication f ~ forward-implication g) ×
    ( backward-implication f ~ backward-implication g)

  ext-iff : (f g : A ↔ B) → (f ＝ g) ≃ htpy-iff f g
  ext-iff f g = equiv-product equiv-funext equiv-funext ∘e equiv-pair-eq f g

  refl-htpy-iff : (f : A ↔ B) → htpy-iff f f
  pr1 (refl-htpy-iff f) = refl-htpy
  pr2 (refl-htpy-iff f) = refl-htpy

  htpy-eq-iff : {f g : A ↔ B} → f ＝ g → htpy-iff f g
  htpy-eq-iff {f} {g} = map-equiv (ext-iff f g)

  eq-htpy-iff : (f g : A ↔ B) → htpy-iff f g → (f ＝ g)
  eq-htpy-iff f g = map-inv-equiv (ext-iff f g)
```

### Logical equivalences between propositions induce equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-has-converse-is-prop :
      is-prop A → is-prop B → {f : A → B} → (B → A) → is-equiv f
    is-equiv-has-converse-is-prop is-prop-A is-prop-B {f} g =
      is-equiv-is-invertible
        ( g)
        ( λ y → eq-is-prop is-prop-B)
        ( λ x → eq-is-prop is-prop-A)

  abstract
    equiv-iff-is-prop : is-prop A → is-prop B → (A → B) → (B → A) → A ≃ B
    pr1 (equiv-iff-is-prop is-prop-A is-prop-B f g) = f
    pr2 (equiv-iff-is-prop is-prop-A is-prop-B f g) =
      is-equiv-has-converse-is-prop is-prop-A is-prop-B g

module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  abstract
    is-equiv-has-converse :
      {f : type-Prop P → type-Prop Q} → (type-Prop Q → type-Prop P) → is-equiv f
    is-equiv-has-converse =
      is-equiv-has-converse-is-prop
        ( is-prop-type-Prop P)
        ( is-prop-type-Prop Q)

  equiv-iff' : type-Prop (P ⇔ Q) → (type-Prop P ≃ type-Prop Q)
  pr1 (equiv-iff' t) = forward-implication t
  pr2 (equiv-iff' t) =
    is-equiv-has-converse-is-prop
      ( is-prop-type-Prop P)
      ( is-prop-type-Prop Q)
      ( backward-implication t)

  equiv-iff :
    (type-Prop P → type-Prop Q) → (type-Prop Q → type-Prop P) →
    type-Prop P ≃ type-Prop Q
  equiv-iff f g = equiv-iff' (f , g)
```

### Equivalences are logical equivalences

```agda
iff-equiv : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A ≃ B) → (A ↔ B)
pr1 (iff-equiv e) = map-equiv e
pr2 (iff-equiv e) = map-inv-equiv e

iff-equiv' : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A ≃ B) → (B ↔ A)
pr1 (iff-equiv' e) = map-inv-equiv e
pr2 (iff-equiv' e) = map-equiv e

is-injective-iff-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-injective (iff-equiv {A = A} {B})
is-injective-iff-equiv p = eq-htpy-equiv (pr1 (htpy-eq-iff p))

compute-fiber-iff-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} ((f , g) : A ↔ B) →
  fiber (iff-equiv) (f , g) ≃ Σ (is-equiv f) (λ f' → map-inv-is-equiv f' ~ g)
compute-fiber-iff-equiv {A = A} {B} (f , g) =
  ( equiv-tot (λ _ → equiv-funext)) ∘e
  ( left-unit-law-Σ-is-contr (is-torsorial-Id' f) (f , refl)) ∘e
  ( inv-associative-Σ) ∘e
  ( equiv-tot (λ _ → equiv-left-swap-Σ)) ∘e
  ( associative-Σ) ∘e
  ( equiv-tot (λ e → equiv-pair-eq (iff-equiv e) (f , g)))
```

### Two equal propositions are logically equivalent

```agda
iff-eq : {l1 : Level} {P Q : Prop l1} → P ＝ Q → type-Prop (P ⇔ Q)
pr1 (iff-eq refl) = id
pr2 (iff-eq refl) = id
```

### Logical equivalence of propositions is equivalent to equivalence of propositions

```agda
abstract
  is-equiv-equiv-iff :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-equiv (equiv-iff' P Q)
  is-equiv-equiv-iff P Q =
    is-equiv-has-converse-is-prop
      ( is-prop-iff-Prop P Q)
      ( is-prop-type-equiv-Prop P Q)
      ( iff-equiv)

equiv-equiv-iff :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  (type-Prop P ↔ type-Prop Q) ≃ (type-Prop P ≃ type-Prop Q)
pr1 (equiv-equiv-iff P Q) = equiv-iff' P Q
pr2 (equiv-equiv-iff P Q) = is-equiv-equiv-iff P Q
```

## Logical equivalences between dependent function types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  iff-Π-iff-family : ((i : I) → A i ↔ B i) → ((i : I) → A i) ↔ ((i : I) → B i)
  pr1 (iff-Π-iff-family e) a i = forward-implication (e i) (a i)
  pr2 (iff-Π-iff-family e) b i = backward-implication (e i) (b i)
```

## Reasoning with logical equivalences

Logical equivalences can be constructed by equational reasoning in the following
way:

```text
logical-equivalence-reasoning
  X ↔ Y by equiv-1
    ↔ Z by equiv-2
    ↔ V by equiv-3
```

```agda
infixl 1 logical-equivalence-reasoning_
infixl 0 step-logical-equivalence-reasoning

logical-equivalence-reasoning_ :
  {l1 : Level} (X : UU l1) → X ↔ X
pr1 (logical-equivalence-reasoning X) = id
pr2 (logical-equivalence-reasoning X) = id

step-logical-equivalence-reasoning :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (X ↔ Y) → (Z : UU l3) → (Y ↔ Z) → (X ↔ Z)
step-logical-equivalence-reasoning e Z f = f ∘iff e

syntax step-logical-equivalence-reasoning e Z f = e ↔ Z by f
```
