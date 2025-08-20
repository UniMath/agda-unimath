# Segal types

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.segal-types
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-function-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-maps
open import orthogonal-factorization-systems.types-local-at-maps

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.compositions-of-directed-edges I
open import simplicial-type-theory.cubes I
open import simplicial-type-theory.directed-interval I
open import simplicial-type-theory.inequality-directed-interval-type I
open import simplicial-type-theory.natural-transformations I

open import synthetic-homotopy-theory.joins-of-types
```

</details>

> This page is present for archiving purposes. It is out of date with the
> library and not being type checked.

## Definition

```text
is-segal : {l : Level} → UU l → UU l
is-segal A = (fg : Λ²₁ → A) → is-contr (composition-horn fg)

is-inner-family : {l1 l2 : Level} {X : UU l1} (A : X → UU l2) → UU (l1 ⊔ l2)
is-inner-family {X = X} A = (x : X) → is-segal (A x)
```

### The type of Segal types

```text
Segal : (l : Level) → UU (lsuc l)
Segal l = Σ (UU l) (is-segal)

Inner-Family : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Inner-Family l1 l2 = Σ (UU l1) (λ X → Σ (X → UU l2) (is-inner-family))
```

In general, the type of Segal types is not itself Segal.

### The composition operation on a Segal type

```text
module _
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  where

  composition-horn-is-segal : (fg : Λ²₁ → A) → composition-horn fg
  composition-horn-is-segal fg = center (is-segal-A fg)

  composition-arrow-is-segal :
    (f g : arrow A) (p : f 1₂ ＝ g 0₂) → composition-horn (rec-arrow-Λ²₁ f g p)
  composition-arrow-is-segal f g p = center (is-segal-A (rec-arrow-Λ²₁ f g p))

  composition-is-segal :
    {x y z : A} (f : hom x y) (g : hom y z) → composition f g
  composition-is-segal f g = composition-horn-is-segal (rec-hom-Λ²₁ f g)

  comp-horn-is-segal : (Λ²₁ → A) → arrow A
  comp-horn-is-segal fg =
    arrow-composite-composition-horn fg (composition-horn-is-segal fg)

  comp-arrow-is-segal :
    (f g : arrow A) (p : f 1₂ ＝ g 0₂) → arrow A
  comp-arrow-is-segal f g p =
    arrow-composite-composition-horn
      ( rec-arrow-Λ²₁ f g p)
      ( composition-horn-is-segal (rec-arrow-Λ²₁ f g p))

  comp-is-segal : {x y z : A} → hom x y → hom y z → hom x z
  comp-is-segal f g = composite-composition f g (composition-is-segal f g)

  witness-composition-horn-is-segal : (Λ²₁ → A) → Δ 2 → A
  witness-composition-horn-is-segal fg =
    witness-composition-horn (composition-horn-is-segal fg)

  witness-composition-arrow-is-segal : (f g : arrow A) (p : f 1₂ ＝ g 0₂) → Δ 2 → A
  witness-composition-arrow-is-segal f g p =
    witness-composition-arrow (composition-arrow-is-segal f g p)

  witness-composition-is-segal : {x y z : A} → hom x y → hom y z → Δ 2 → A
  witness-composition-is-segal f g =
    witness-composition f g (composition-is-segal f g)

  unique-composite-horn-is-segal :
    (fg : Λ²₁ → A) (h : Δ¹ → A) →
    is-composite-horn fg h → comp-horn-is-segal fg ＝ h
  unique-composite-horn-is-segal fg h (c , p) =
    ap (arrow-composite-composition-horn fg) (contraction (is-segal-A fg) c) ∙ p

  unique-composite-arrow-is-segal :
    (f g : Δ¹ → A) (p : f 1₂ ＝ g 0₂) (h : Δ¹ → A) →
    is-composite-arrow f g p h → comp-arrow-is-segal f g p ＝ h
  unique-composite-arrow-is-segal f g p =
    unique-composite-horn-is-segal (rec-arrow-Λ²₁ f g p)

  unique-composite-is-segal :
    {x y z : A}
    (f : hom x y) (g : hom y z) (h : hom x z) →
    is-composite f g h → comp-is-segal f g ＝ h
  unique-composite-is-segal f g h (c , p) =
    ( ap
      ( composite-composition f g)
      ( contraction (is-segal-A (rec-hom-Λ²₁ f g)) c)) ∙
    ( p)
```

#### Computing with segal composition

```text
module _
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  where

  compute-first-witness-composition-is-segal :
    {x y z : A} (f : hom x y) (g : hom y z)
    (t : Δ¹) {r : predicate-Δ 2 (t , 0₂)} →
    ( witness-composition-is-segal is-segal-A f g ((t , 0₂) , r)) ＝
    ( arrow-hom f t)
  compute-first-witness-composition-is-segal f g =
    compute-first-witness-composition f g
      ( composition-is-segal is-segal-A f g)

  compute-second-witness-composition-is-segal :
    {x y z : A} (f : hom x y) (g : hom y z)
    (t : Δ¹) {r : predicate-Δ 2 (1₂ , t)} →
    ( witness-composition-is-segal is-segal-A f g ((1₂ , t) , r)) ＝
    ( arrow-hom g t)
  compute-second-witness-composition-is-segal f g =
    compute-second-witness-composition f g
      ( composition-is-segal is-segal-A f g)
```

## Properties

### The Segal condition is a proposition

```text
is-prop-is-segal : {l : Level} (A : UU l) → is-prop (is-segal A)
is-prop-is-segal A = is-prop-Π (λ _ → is-property-is-contr)

is-segal-Prop : {l : Level} (A : UU l) → Prop l
pr1 (is-segal-Prop A) = is-segal A
pr2 (is-segal-Prop A) = is-prop-is-segal A

is-prop-is-inner-family :
  {l1 l2 : Level} {X : UU l1} (A : X → UU l2) → is-prop (is-inner-family A)
is-prop-is-inner-family A = is-prop-Π (is-prop-is-segal ∘ A)

is-inner-family-Prop :
  {l1 l2 : Level} {X : UU l1} (A : X → UU l2) → Prop (l1 ⊔ l2)
pr1 (is-inner-family-Prop A) = is-inner-family A
pr2 (is-inner-family-Prop A) = is-prop-is-inner-family A
```

### Being Segal is equivalent to being $(Λ²₁ ↪ Δ²)$-local

```text
equiv-is-segal-is-Λ²₁↪Δ²-local :
  {l : Level} (A : UU l) → is-local Λ²₁→Δ² A ≃ is-segal A
equiv-is-segal-is-Λ²₁↪Δ²-local A =
  equiv-is-contr-extension-dependent-type-is-local-dependent-type Λ²₁→Δ² (λ _ → A)

is-segal-is-Λ²₁↪Δ²-local :
  {l : Level} (A : UU l) → is-local Λ²₁→Δ² A → is-segal A
is-segal-is-Λ²₁↪Δ²-local = map-equiv ∘ equiv-is-segal-is-Λ²₁↪Δ²-local

is-Λ²₁↪Δ²-local-is-segal :
  {l : Level} (A : UU l) → is-segal A → is-local Λ²₁→Δ² A
is-Λ²₁↪Δ²-local-is-segal = map-inv-equiv ∘ equiv-is-segal-is-Λ²₁↪Δ²-local
```

### The Π-type is Segal if the type family is inner

```text
is-segal-Π :
  {l1 l2 : Level} {X : UU l1} {A : X → UU l2} →
  is-inner-family A → is-segal ((x : X) → A x)
is-segal-Π {X = X} {A} is-inner-A =
    is-segal-is-Λ²₁↪Δ²-local ((x : X) → A x)
      ( map-distributive-Π-is-local-dependent-type Λ²₁→Δ²
        ( λ x _ → A x)
        ( λ x → is-Λ²₁↪Δ²-local-is-segal (A x) (is-inner-A x)))

is-segal-function-type :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} →
  is-segal A → is-segal (X → A)
is-segal-function-type is-segal-A = is-segal-Π (λ _ → is-segal-A)
-- TODO: functoriality
-- TODO: homotopy is homotopy
```

As a corollary, the type of arrows in a Segal type is also Segal.

```text
vertical-comp-is-segal :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} → is-segal A →
  {f g h : X → A} → nat f g → nat g h → nat f h
vertical-comp-is-segal is-segal-A α β t =
  comp-is-segal is-segal-A (α t) (β t)

is-segal-arrow : {l : Level} {A : UU l} → is-segal A → is-segal (arrow A)
is-segal-arrow = is-segal-function-type
```
