# Compositions of directed edges

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.compositions-of-directed-edges
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-booleans
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-maps

open import simplicial-type-theory.2-simplices I
open import simplicial-type-theory.arrows I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
open import simplicial-type-theory.inequality-directed-interval I
open import simplicial-type-theory.inner-2-horn I
open import simplicial-type-theory.standard-simplices I

open import synthetic-homotopy-theory.joins-of-types
```

</details>

## Idea

Given a pair of consecutive
[directed edges](simplicial-type-theory.directed-edges.md)

```text
      f       g
  x ----> y ----> z
```

in a type `A`, then a
{{#concept "composite" Disambiguation="of directed edges in a simplicial type"}}
is a 2-simplex

```text
  σ : Δ² → A
```

such that the restriction along the first axis is `f` and the restriction along
the second axis is `g`.

## Definitions

### Compositions

```agda
dependent-composition-horn :
  {l : Level} (A : Δ 2 → UU l) →
  ((u : Λ²₁) → A (inclusion-Δ²-Λ²₁ u)) → UU (I1 ⊔ I2 ⊔ l)
dependent-composition-horn A =
  extension-dependent-type inclusion-Δ²-Λ²₁ A

module _
  {l : Level} {A : UU l}
  where

  composition-horn : (Λ²₁ → A) → UU (I1 ⊔ I2 ⊔ l)
  composition-horn = dependent-composition-horn (λ _ → A)

  composition-arrow : (f g : arrow▵ A) → f 1▵ ＝ g 0▵ → UU (I1 ⊔ I2 ⊔ l)
  composition-arrow f g p = composition-horn (rec-arrow-Λ²₁ f g p)

  composition : {x y z : A} → hom▵ x y → hom▵ y z → UU (I1 ⊔ I2 ⊔ l)
  composition f g = composition-horn (rec-hom-Λ²₁ f g)
```

### Composition witnesses

```agda
module _
  {l : Level} {A : UU l}
  where

  witness-composition-horn :
    {fg : Λ²₁ → A} → composition-horn fg → Δ 2 → A
  witness-composition-horn = pr1

  witness-composition-arrow :
    {f g : arrow▵ A} {p : f 1▵ ＝ g 0▵} → composition-arrow f g p → Δ 2 → A
  witness-composition-arrow = pr1

  witness-composition :
    {x y z : A} (f : hom▵ x y) (g : hom▵ y z) → composition f g → Δ 2 → A
  witness-composition f g = pr1
```

### Extension witnesses compositions

```agda
module _
  {l : Level} {A : UU l}
  where

  htpy-composition-horn :
    {fg : Λ²₁ → A} (c : composition-horn fg) →
    fg ~ witness-composition-horn c ∘ inclusion-Δ²-Λ²₁
  htpy-composition-horn = pr2

  htpy-composition-arrow :
    {f g : arrow▵ A} {p : f 1▵ ＝ g 0▵} (c : composition-arrow f g p) →
    rec-arrow-Λ²₁ f g p ~ witness-composition-arrow c ∘ inclusion-Δ²-Λ²₁
  htpy-composition-arrow = pr2

  htpy-composition :
    {x y z : A} (f : hom▵ x y) (g : hom▵ y z) (c : composition f g) →
    rec-hom-Λ²₁ f g ~ witness-composition f g c ∘ inclusion-Δ²-Λ²₁
  htpy-composition f g = pr2
```

### Composites

```agda
module _
  {l : Level} {A : UU l}
  where

  arrow-composite-composition-horn :
    (fg : Λ²₁ → A) → composition-horn fg → arrow▵ A
  arrow-composite-composition-horn fg c t =
    witness-composition-horn c ((t , t) , refl-leq-Δ¹)

  arrow-composite-composition-arrow :
    (f g : arrow▵ A) (p : f 1▵ ＝ g 0▵) → composition-arrow f g p → arrow▵ A
  arrow-composite-composition-arrow f g p =
    arrow-composite-composition-horn (rec-arrow-Λ²₁ f g p)

  eq-source-arrow-composite-composition-arrow :
    (f g : arrow▵ A) (p : f 1▵ ＝ g 0▵) (c : composition-arrow f g p) →
    arrow-composite-composition-arrow f g p c 0▵ ＝ f 0▵
  eq-source-arrow-composite-composition-arrow f g p c =
    ( ap (witness-composition-arrow c) (eq-type-subtype (subtype-Δ 2) refl)) ∙
    ( inv (htpy-composition-arrow c ((0▵ , 0▵) , inl-join refl))) ∙
    ( compute-inl-cogap-join _ refl)

  eq-target-arrow-composite-composition-arrow :
    (f g : arrow▵ A) (p : f 1▵ ＝ g 0▵) (c : composition-arrow f g p) →
    arrow-composite-composition-arrow f g p c 1▵ ＝ g 1▵
  eq-target-arrow-composite-composition-arrow f g p c =
    ( ap (witness-composition-arrow c) (eq-type-subtype (subtype-Δ 2) refl)) ∙
    ( inv (htpy-composition-arrow c ((1▵ , 1▵) , inr-join refl))) ∙
    ( compute-inr-cogap-join _ refl)

  composite-composition-arrow :
    (f g : arrow▵ A) (p : f 1▵ ＝ g 0▵) →
    composition-arrow f g p → hom▵ (f 0▵) (g 1▵)
  composite-composition-arrow f g p c =
    ( arrow-composite-composition-arrow f g p c ,
      eq-source-arrow-composite-composition-arrow f g p c ,
      eq-target-arrow-composite-composition-arrow f g p c)
```

```agda
  arrow-composite-composition :
    {x y z : A} (f : hom▵ x y) (g : hom▵ y z) → composition f g → arrow▵ A
  arrow-composite-composition f g =
    arrow-composite-composition-horn (rec-hom-Λ²₁ f g)

  eq-source-arrow-composite-composition :
    {x y z : A} (f : hom▵ x y) (g : hom▵ y z) (c : composition f g) →
    arrow-composite-composition f g c 0▵ ＝ x
  eq-source-arrow-composite-composition f g c =
    ( eq-source-arrow-composite-composition-arrow
      ( arrow-hom▵ f) (arrow-hom▵ g) (eq-source-target-hom▵ f g) c) ∙
    ( eq-source-hom▵ f)

  eq-target-arrow-composite-composition :
    {x y z : A} (f : hom▵ x y) (g : hom▵ y z) (c : composition f g) →
    arrow-composite-composition f g c 1▵ ＝ z
  eq-target-arrow-composite-composition f g c =
    ( eq-target-arrow-composite-composition-arrow
      ( arrow-hom▵ f)
      ( arrow-hom▵ g)
      ( eq-source-target-hom▵ f g)
      ( c)) ∙
    ( eq-target-hom▵ g)

  composite-composition :
    {x y z : A} (f : hom▵ x y) (g : hom▵ y z) → composition f g → hom▵ x z
  composite-composition f g c =
    ( arrow-composite-composition-horn (rec-hom-Λ²₁ f g) c ,
      eq-source-arrow-composite-composition f g c ,
      eq-target-arrow-composite-composition f g c)
```

## Computations

### Extensionality of compositions

```agda
module _
  {l : Level} {A : Δ 2 → UU l}
  where

  extensionality-composition-horn :
    (i : (u : Λ²₁) → A (inclusion-Δ²-Λ²₁ u))
    (c d : dependent-composition-horn A i) →
    (c ＝ d) ≃ htpy-extension inclusion-Δ²-Λ²₁ i c d
  extensionality-composition-horn = extensionality-extension inclusion-Δ²-Λ²₁

  eq-htpy-composition-horn :
    (i : (u : Λ²₁) → A (inclusion-Δ²-Λ²₁ u))
    (c d : dependent-composition-horn A i)
    (H : map-extension c ~ map-extension d) →
    coherence-htpy-extension inclusion-Δ²-Λ²₁ i c d H →
    c ＝ d
  eq-htpy-composition-horn = eq-htpy-extension inclusion-Δ²-Λ²₁

  htpy-eq-composition-horn :
    (i : (u : Λ²₁) → A (inclusion-Δ²-Λ²₁ u))
    (c d : dependent-composition-horn A i) →
    c ＝ d → htpy-extension inclusion-Δ²-Λ²₁ i c d
  htpy-eq-composition-horn = htpy-eq-extension inclusion-Δ²-Λ²₁
```

### Computing with composition witnesses

```agda
module _
  {l : Level} {A : UU l}
  where

  compute-first-witness-composition-arrow :
    (f g : arrow▵ A) (p : f 1▵ ＝ g 0▵)
    (c : composition-arrow f g p) →
    (t : Δ¹) {r : is-in-Δ 2 (t , 0▵)} →
    witness-composition-arrow c ((t , 0▵) , r) ＝ f t
  compute-first-witness-composition-arrow f g p c t =
    ( ap
      ( λ r → witness-composition-arrow c ((t , 0▵) , r))
      ( eq-is-in-subtype (subtype-Δ 2))) ∙
    ( inv (pr2 c ((t , 0▵) , inl-join refl))) ∙
    ( compute-inl-rec-arrow-Λ²₁ f g p t)

  compute-second-witness-composition-arrow :
    (f g : arrow▵ A) (p : f 1▵ ＝ g 0▵)
    (c : composition-arrow f g p) →
    (t : Δ¹) {r : is-in-Δ 2 (1▵ , t)} →
    witness-composition-arrow c ((1▵ , t) , r) ＝ g t
  compute-second-witness-composition-arrow f g p c t =
    ( ap
      ( λ r → witness-composition-arrow c ((1▵ , t) , r))
      ( eq-is-in-subtype (subtype-Δ 2))) ∙
    ( inv (pr2 c ((1▵ , t) , inr-join refl))) ∙
    ( compute-inr-rec-arrow-Λ²₁ f g p t)

  compute-first-witness-composition :
      {x y z : A} (f : hom▵ x y) (g : hom▵ y z)
      (c : composition f g) →
      (t : Δ¹) {r : is-in-Δ 2 (t , 0▵)} →
      witness-composition f g c ((t , 0▵) , r) ＝ arrow-hom▵ f t
  compute-first-witness-composition f g =
    compute-first-witness-composition-arrow
      (arrow-hom▵ f) (arrow-hom▵ g) (eq-source-target-hom▵ f g)

  compute-second-witness-composition :
      {x y z : A} (f : hom▵ x y) (g : hom▵ y z) (c : composition f g) →
      (t : Δ¹) {r : is-in-Δ 2 (1▵ , t)} →
      witness-composition f g c ((1▵ , t) , r) ＝ arrow-hom▵ g t
  compute-second-witness-composition f g =
    compute-second-witness-composition-arrow
      (arrow-hom▵ f) (arrow-hom▵ g) (eq-source-target-hom▵ f g)
```

### The `is-composite-hom` family

An arrow `h` is the **composite** of `f` and `g` if there is a composition of
`f` and `g` such that their composite is equal to `h`.

```agda
module _
  {l : Level} {A : UU l} (fg : Λ²₁ → A) (h : Δ¹ → A)
  where

  is-composite-horn : UU (I1 ⊔ I2 ⊔ l)
  is-composite-horn =
    Σ (composition-horn fg) (λ c → arrow-composite-composition-horn fg c ＝ h)

  triangle-horn :
    fg ((0▵ , 0▵) , inl-join refl) ＝ h 0▵ →
    fg ((1▵ , 1▵) , inr-join refl) ＝ h 1▵ →
    ∂Δ² → A
  triangle-horn h0 h1 =
    rec-arrow-∂Δ²
      ( λ t → fg ((t , 0▵) , inl-join refl))
      ( λ s → fg ((1▵ , s) , inr-join refl))
      ( h)
      ( h0)
      ( ap (λ p → fg ((1▵ , 0▵) , p)) (glue-join (refl , refl)))
      ( h1)

  is-composite-horn' : UU (I1 ⊔ I2 ⊔ l)
  is-composite-horn' =
    Σ ( ( fg ((0▵ , 0▵) , inl-join refl) ＝ h 0▵) ×
        ( fg ((1▵ , 1▵) , inr-join refl) ＝ h 1▵))
      ( λ (h0 , h1) → extension inclusion-∂Δ² (triangle-horn h0 h1))

hom▵² :
  {l : Level} {A : UU l} {x y z : A} →
  hom▵ x y → hom▵ y z → hom▵ x z → UU (I1 ⊔ I2 ⊔ l)
hom▵² f g h = extension inclusion-∂Δ² (rec-hom-∂Δ² f g h)
```

```agda
is-composite-arrow :
  {l : Level} {A : UU l} →
  (f g : arrow▵ A) → f 1▵ ＝ g 0▵ → arrow▵ A → UU (I1 ⊔ I2 ⊔ l)
is-composite-arrow f g p h = is-composite-horn (rec-arrow-Λ²₁ f g p) h
```

These definitions are not compatible in the same way as the previous ones, as
the second formulation also requires coherence at the end points.

```agda
is-composite-hom :
  {l : Level} {A : UU l} {x y z : A} →
  hom▵ x y → hom▵ y z → hom▵ x z → UU (I1 ⊔ I2 ⊔ l)
is-composite-hom f g h =
  Σ (composition f g) (λ c → composite-composition f g c ＝ h)
```
