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
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
open import simplicial-type-theory.inequality-directed-interval I
open import simplicial-type-theory.inner-2-horn I
open import simplicial-type-theory.natural-transformations I
open import simplicial-type-theory.standard-simplices I

open import synthetic-homotopy-theory.joins-of-types
```

</details>

## Idea

A {{#concept "Segal type" Agda=Segal}}, or **∞-precategory**, is a simplicial
type with unique
[compositions](simplicial-type-theory.compositions-of-directed-edges.md).

## Definitions

### Segal types in terms of unique compositions

```agda
is-segal : {l : Level} → UU l → UU (I1 ⊔ I2 ⊔ l)
is-segal A = (fg : Λ²₁ → A) → is-contr (composition-horn fg)

is-segal-family :
  {l1 l2 : Level} {X : UU l1} (A : X → UU l2) → UU (I1 ⊔ I2 ⊔ l1 ⊔ l2)
is-segal-family {X = X} A = (x : X) → is-segal (A x)
```

### The type of Segal types

```agda
Segal : (l : Level) → UU (I1 ⊔ I2 ⊔ lsuc l)
Segal l = Σ (UU l) (is-segal)

Segal-Family : (l1 l2 : Level) → UU (I1 ⊔ I2 ⊔ lsuc l1 ⊔ lsuc l2)
Segal-Family l1 l2 = Σ (UU l1) (λ X → Σ (X → UU l2) (is-segal-family))
```

Note that the type of Segal types is not itself Segal.

### Segal types in terms of locality at the inner horn inclusion

```agda
is-inner-type : {l : Level} → UU l → UU (I1 ⊔ I2 ⊔ l)
is-inner-type = is-local inclusion-Δ²-Λ²₁
```

### The composition operation on a Segal type

```agda
module _
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  where

  composition-horn-is-segal : (fg : Λ²₁ → A) → composition-horn fg
  composition-horn-is-segal fg = center (is-segal-A fg)

  composition-arrow-is-segal :
    (f g : arrow▵ A) (p : f 1▵ ＝ g 0▵) → composition-horn (rec-arrow-Λ²₁ f g p)
  composition-arrow-is-segal f g p = center (is-segal-A (rec-arrow-Λ²₁ f g p))

  composition-is-segal :
    {x y z : A} (f : hom▵ x y) (g : hom▵ y z) → composition f g
  composition-is-segal f g = composition-horn-is-segal (rec-hom-Λ²₁ f g)

  comp-horn-is-segal : (Λ²₁ → A) → arrow▵ A
  comp-horn-is-segal fg =
    arrow-composite-composition-horn fg (composition-horn-is-segal fg)

  comp-arrow-is-segal :
    (f g : arrow▵ A) (p : f 1▵ ＝ g 0▵) → arrow▵ A
  comp-arrow-is-segal f g p =
    arrow-composite-composition-horn
      ( rec-arrow-Λ²₁ f g p)
      ( composition-horn-is-segal (rec-arrow-Λ²₁ f g p))

  comp-is-segal : {x y z : A} → hom▵ x y → hom▵ y z → hom▵ x z
  comp-is-segal f g = composite-composition f g (composition-is-segal f g)

  witness-composition-horn-is-segal : (Λ²₁ → A) → Δ 2 → A
  witness-composition-horn-is-segal fg =
    witness-composition-horn (composition-horn-is-segal fg)

  witness-composition-arrow-is-segal :
    (f g : arrow▵ A) (p : f 1▵ ＝ g 0▵) → Δ 2 → A
  witness-composition-arrow-is-segal f g p =
    witness-composition-arrow (composition-arrow-is-segal f g p)

  witness-composition-is-segal : {x y z : A} → hom▵ x y → hom▵ y z → Δ 2 → A
  witness-composition-is-segal f g =
    witness-composition f g (composition-is-segal f g)

  unique-composite-horn-is-segal :
    (fg : Λ²₁ → A) (h : Δ¹ → A) →
    is-composite-horn fg h → comp-horn-is-segal fg ＝ h
  unique-composite-horn-is-segal fg h (c , p) =
    ap (arrow-composite-composition-horn fg) (contraction (is-segal-A fg) c) ∙ p

  unique-composite-arrow-is-segal :
    (f g : Δ¹ → A) (p : f 1▵ ＝ g 0▵) (h : Δ¹ → A) →
    is-composite-arrow f g p h → comp-arrow-is-segal f g p ＝ h
  unique-composite-arrow-is-segal f g p =
    unique-composite-horn-is-segal (rec-arrow-Λ²₁ f g p)

  unique-composite-is-segal :
    {x y z : A} (f : hom▵ x y) (g : hom▵ y z) (h : hom▵ x z) →
    is-composite-hom f g h → comp-is-segal f g ＝ h
  unique-composite-is-segal f g h (c , p) =
    ( ap
      ( composite-composition f g)
      ( contraction (is-segal-A (rec-hom-Λ²₁ f g)) c)) ∙
    ( p)
```

#### Computing with segal composition

```agda
module _
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  where

  compute-first-witness-composition-is-segal :
    {x y z : A} (f : hom▵ x y) (g : hom▵ y z)
    (t : Δ¹) {r : is-in-Δ 2 (t , 0▵)} →
    ( witness-composition-is-segal is-segal-A f g ((t , 0▵) , r)) ＝
    ( arrow-hom▵ f t)
  compute-first-witness-composition-is-segal f g =
    compute-first-witness-composition f g
      ( composition-is-segal is-segal-A f g)

  compute-second-witness-composition-is-segal :
    {x y z : A} (f : hom▵ x y) (g : hom▵ y z)
    (t : Δ¹) {r : is-in-Δ 2 (1▵ , t)} →
    ( witness-composition-is-segal is-segal-A f g ((1▵ , t) , r)) ＝
    ( arrow-hom▵ g t)
  compute-second-witness-composition-is-segal f g =
    compute-second-witness-composition f g
      ( composition-is-segal is-segal-A f g)
```

## Properties

### The Segal condition is a proposition

```agda
is-prop-is-segal : {l : Level} (A : UU l) → is-prop (is-segal A)
is-prop-is-segal A = is-prop-Π (λ _ → is-property-is-contr)

is-segal-Prop : {l : Level} (A : UU l) → Prop (I1 ⊔ I2 ⊔ l)
pr1 (is-segal-Prop A) = is-segal A
pr2 (is-segal-Prop A) = is-prop-is-segal A

is-prop-is-segal-family :
  {l1 l2 : Level} {X : UU l1} (A : X → UU l2) → is-prop (is-segal-family A)
is-prop-is-segal-family A = is-prop-Π (is-prop-is-segal ∘ A)

is-segal-family-Prop :
  {l1 l2 : Level} {X : UU l1} (A : X → UU l2) → Prop (I1 ⊔ I2 ⊔ l1 ⊔ l2)
pr1 (is-segal-family-Prop A) = is-segal-family A
pr2 (is-segal-family-Prop A) = is-prop-is-segal-family A
```

### Being Segal is equivalent to being $(Λ²₁ ↪ Δ²)$-local

```agda
module _
  {l : Level} (A : UU l)
  where

  equiv-is-segal-is-inner-type : is-inner-type A ≃ is-segal A
  equiv-is-segal-is-inner-type =
    equiv-is-contr-extension-dependent-type-is-local-dependent-type
      ( inclusion-Δ²-Λ²₁)
      ( λ _ → A)

  is-segal-is-inner-type : is-inner-type A → is-segal A
  is-segal-is-inner-type = map-equiv equiv-is-segal-is-inner-type

  is-inner-type-is-segal : is-segal A → is-inner-type A
  is-inner-type-is-segal = map-inv-equiv equiv-is-segal-is-inner-type
```

### The Π-type is Segal if the type family is Segal

```agda
module _
  {l1 l2 : Level} {X : UU l1}
  where

  is-segal-Π :
    {A : X → UU l2} → is-segal-family A → is-segal ((x : X) → A x)
  is-segal-Π {A} is-inner-A =
      is-segal-is-inner-type ((x : X) → A x)
        ( distributive-Π-is-local-dependent-type inclusion-Δ²-Λ²₁
          ( λ x _ → A x)
          ( λ x → is-inner-type-is-segal (A x) (is-inner-A x)))

  is-segal-function-type :
    {A : UU l2} → is-segal A → is-segal (X → A)
  is-segal-function-type is-segal-A = is-segal-Π (λ _ → is-segal-A)
```

As a corollary, the type of arrows in a Segal type is also Segal.

```agda
vertical-comp-is-segal :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} → is-segal A →
  {f g h : X → A} → f ⇒▵ g → g ⇒▵ h → f ⇒▵ h
vertical-comp-is-segal is-segal-A α β t =
  comp-is-segal is-segal-A (α t) (β t)

is-segal-arrow : {l : Level} {A : UU l} → is-segal A → is-segal (arrow▵ A)
is-segal-arrow = is-segal-function-type
```

### Propositions are Segal

```agda
module _
  {l : Level} {A : UU l}
  where

  is-inner-type-is-prop : is-prop A → is-inner-type A
  is-inner-type-is-prop H =
    is-local-has-element-domain-is-prop inclusion-Δ²-Λ²₁ A H (inl-Λ²₁ 0▵)

  is-segal-is-prop : is-prop A → is-segal A
  is-segal-is-prop H = is-segal-is-inner-type A (is-inner-type-is-prop H)
```
