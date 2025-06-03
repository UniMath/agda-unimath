# Compositions of directed edges

```agda
module simplicial-type-theory.compositions-of-directed-edges where
```

<details><summary>Imports</summary>

```agda
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
open import foundation.torsorial-type-families
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-booleans
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-maps

open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.inner-2-horn
open import simplicial-type-theory.standard-simplices
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

## Definition

```text
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  composition-hom▵ : hom▵ y z → hom▵ x y → UU l
  composition-hom▵ g f = Σ (Δ 2 → A) (λ σ → {!   !})
```

A composition of two arrows `f : x → y` and `g: y → z` in a type `A` is a
2-simplex that restricts on the boundary to `f` and `g` as follows.

```md
           z
          ^^
        /..|
      /....g
    /......|
  x - f -> y
```

The diagonal arrow is then a composite of `g` after `f`.

## Definitions

### Compositions

```text
dependent-composition-horn :
  {l : Level} (A : Δ 2 → UU l) → ((u : Λ²₁) → A (inclusion-Δ²-Λ²₁ u)) → UU l
dependent-composition-horn A = extension-dependent-type inclusion-Δ²-Λ²₁ A

module _
  {l : Level} {A : UU l}
  where

  composition-horn : (Λ²₁ → A) → UU l
  composition-horn = dependent-composition-horn (λ _ → A)

  composition-arr : (f g : arrow▵ A) → f 1₂ ＝ g 0₂ → UU l
  composition-arr f g p = composition-horn (rec-arr-Λ²₁ f g p)

  composition : {x y z : A} → hom x y → hom y z → UU l
  composition f g = composition-horn (rec-hom-Λ²₁ f g)
```

### Composition witnesses

```text
module _
  {l : Level} {A : UU l}
  where

  witness-composition-horn :
    {fg : Λ²₁ → A} → composition-horn fg → Δ 2 → A
  witness-composition-horn = pr1

  witness-composition-arr :
    {f g : arr A} {p : f 1₂ ＝ g 0₂} → composition-arr f g p → Δ 2 → A
  witness-composition-arr = pr1

  witness-composition :
    {x y z : A} (f : hom x y) (g : hom y z) → composition f g → Δ 2 → A
  witness-composition f g = pr1
```

### Extension witnesses compositions

```text
module _
  {l : Level} {A : UU l}
  where

  htpy-composition-horn :
    {fg : Λ²₁ → A} (c : composition-horn fg) →
    fg ~ witness-composition-horn c ∘ inclusion-Δ²-Λ²₁
  htpy-composition-horn = pr2

  htpy-composition-arr :
    {f g : arr A} {p : f 1₂ ＝ g 0₂} (c : composition-arr f g p) →
    rec-arr-Λ²₁ f g p ~ witness-composition-arr c ∘ inclusion-Δ²-Λ²₁
  htpy-composition-arr = pr2

  htpy-composition :
    {x y z : A} (f : hom x y) (g : hom y z) (c : composition f g) →
    rec-hom-Λ²₁ f g ~ witness-composition f g c ∘ inclusion-Δ²-Λ²₁
  htpy-composition f g = pr2
```

### Composites

```text
module _
  {l : Level} {A : UU l}
  where

  arr-composite-composition-horn :
    (fg : Λ²₁ → A) → composition-horn fg → arr A
  arr-composite-composition-horn fg c t =
    witness-composition-horn c ((t , t) , refl-≤)

  arr-composite-composition-arr :
    (f g : arr A) (p : f 1₂ ＝ g 0₂) → composition-arr f g p → arr A
  arr-composite-composition-arr f g p =
    arr-composite-composition-horn (rec-arr-Λ²₁ f g p)

  eq-source-arr-composite-composition-arr :
    (f g : arr A) (p : f 1₂ ＝ g 0₂) (c : composition-arr f g p) →
    arr-composite-composition-arr f g p c 0₂ ＝ f 0₂
  eq-source-arr-composite-composition-arr f g p c =
    ( ap (witness-composition-arr c) (eq-type-subtype (subtype-Δ 2) refl)) ∙
    ( inv (htpy-composition-arr c ((0₂ , 0₂) , inl-join refl))) ∙
    ( compute-inl-cogap-join _ refl)

  eq-target-arr-composite-composition-arr :
    (f g : arr A) (p : f 1₂ ＝ g 0₂) (c : composition-arr f g p) →
    arr-composite-composition-arr f g p c 1₂ ＝ g 1₂
  eq-target-arr-composite-composition-arr f g p c =
    ( ap (witness-composition-arr c) (eq-type-subtype (subtype-Δ 2) refl)) ∙
    ( inv (htpy-composition-arr c ((1₂ , 1₂) , inr-join refl))) ∙
    ( compute-inr-cogap-join _ refl)

  composite-composition-arr :
    (f g : arr A) (p : f 1₂ ＝ g 0₂) → composition-arr f g p → hom (f 0₂) (g 1₂)
  pr1 (composite-composition-arr f g p c) =
    arr-composite-composition-arr f g p c
  pr1 (pr2 (composite-composition-arr f g p c)) =
    eq-source-arr-composite-composition-arr f g p c
  pr2 (pr2 (composite-composition-arr f g p c)) =
    eq-target-arr-composite-composition-arr f g p c
```

```text
  arr-composite-composition :
    {x y z : A} (f : hom x y) (g : hom y z) → composition f g → arr A
  arr-composite-composition f g =
    arr-composite-composition-horn (rec-hom-Λ²₁ f g)

  eq-source-arr-composite-composition :
    {x y z : A} (f : hom x y) (g : hom y z) (c : composition f g) →
    arr-composite-composition f g c 0₂ ＝ x
  eq-source-arr-composite-composition f g c =
    ( eq-source-arr-composite-composition-arr
      ( arr-hom f) (arr-hom g) (eq-source-target-hom f g) c) ∙
    ( eq-source-hom f)

  eq-target-arr-composite-composition :
    {x y z : A} (f : hom x y) (g : hom y z) (c : composition f g) →
    arr-composite-composition f g c 1₂ ＝ z
  eq-target-arr-composite-composition f g c =
    ( eq-target-arr-composite-composition-arr
      ( arr-hom f) (arr-hom g) (eq-source-target-hom f g) c) ∙
    ( eq-target-hom g)

  composite-composition :
    {x y z : A} (f : hom x y) (g : hom y z) → composition f g → hom x z
  pr1 (composite-composition f g c) =
    arr-composite-composition-horn (rec-hom-Λ²₁ f g) c
  pr1 (pr2 (composite-composition f g c)) =
    eq-source-arr-composite-composition f g c
  pr2 (pr2 (composite-composition f g c)) =
    eq-target-arr-composite-composition f g c
```

## Computations

### Extensionality of compositions

```text
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
    coherence-htpy-extension inclusion-Δ²-Λ²₁ i c d H → c ＝ d
  eq-htpy-composition-horn = eq-htpy-extension inclusion-Δ²-Λ²₁

  htpy-eq-composition-horn :
    (i : (u : Λ²₁) → A (inclusion-Δ²-Λ²₁ u))
    (c d : dependent-composition-horn A i) →
    c ＝ d → htpy-extension inclusion-Δ²-Λ²₁ i c d
  htpy-eq-composition-horn = htpy-eq-extension inclusion-Δ²-Λ²₁
```

### Computing with composition witnesses

```text
module _
  {l : Level} {A : UU l}
  where

  compute-first-witness-composition-arr :
    (f g : arr A) (p : f 1₂ ＝ g 0₂) (c : composition-arr f g p) →
    (t : 𝟚) {r : predicate-Δ 2 (t , 0₂)} →
    witness-composition-arr c ((t , 0₂) , r) ＝ f t
  compute-first-witness-composition-arr f g p c t =
    ( ap
      ( λ r → witness-composition-arr c ((t , 0₂) , r))
      ( eq-is-in-subtype (subtype-Δ 2))) ∙
    ( inv (pr2 c ((t , 0₂) , inl-join refl))) ∙
    ( compute-first-rec-arr-Λ²₁ f g p t)

  compute-second-witness-composition-arr :
    (f g : arr A) (p : f 1₂ ＝ g 0₂) (c : composition-arr f g p) →
    (t : 𝟚) {r : predicate-Δ 2 (1₂ , t)} →
    witness-composition-arr c ((1₂ , t) , r) ＝ g t
  compute-second-witness-composition-arr f g p c t =
    ( ap
      ( λ r → witness-composition-arr c ((1₂ , t) , r))
      ( eq-is-in-subtype (subtype-Δ 2))) ∙
    ( inv (pr2 c ((1₂ , t) , inr-join refl))) ∙
    ( compute-second-rec-arr-Λ²₁ f g p t)

  compute-first-witness-composition :
      {x y z : A} (f : hom x y) (g : hom y z) (c : composition f g) →
      (t : 𝟚) {r : predicate-Δ 2 (t , 0₂)} →
      witness-composition f g c ((t , 0₂) , r) ＝ arr-hom f t
  compute-first-witness-composition f g =
    compute-first-witness-composition-arr
      (arr-hom f) (arr-hom g) (eq-source-target-hom f g)

  compute-second-witness-composition :
      {x y z : A} (f : hom x y) (g : hom y z) (c : composition f g) →
      (t : 𝟚) {r : predicate-Δ 2 (1₂ , t)} →
      witness-composition f g c ((1₂ , t) , r) ＝ arr-hom g t
  compute-second-witness-composition f g =
    compute-second-witness-composition-arr
      (arr-hom f) (arr-hom g) (eq-source-target-hom f g)
```

TODO: move part below

### The `is-composite` family

An arrow `h` is the **composite** of `f` and `g` if there is a composition of
`f` and `g` such that their composite is equal to `h`.

```text
module _
  {l : Level} {A : UU l} (fg : Λ²₁ → A) (h : 𝟚 → A)
  where

  is-composite-horn : UU l
  is-composite-horn =
    Σ (composition-horn fg) (λ c → arr-composite-composition-horn fg c ＝ h)

  triangle-horn :
    fg ((0₂ , 0₂) , inl-join refl) ＝ h 0₂ →
    fg ((1₂ , 1₂) , inr-join refl) ＝ h 1₂ →
    ∂Δ² → A
  triangle-horn h0 h1 =
    rec-arr-∂Δ²
      ( λ t → fg ((t , 0₂) , inl-join refl))
      ( λ s → fg ((1₂ , s) , inr-join refl))
      ( h)
      ( h0)
      ( ap (λ p → fg ((1₂ , 0₂) , p)) (glue-join (refl , refl)))
      ( h1)

  is-composite-horn' : UU l
  is-composite-horn' =
    Σ ( ( fg ((0₂ , 0₂) , inl-join refl) ＝ h 0₂) ×
        ( fg ((1₂ , 1₂) , inr-join refl) ＝ h 1₂))
      ( λ (h0 , h1) → extension ∂Δ²→Δ² (triangle-horn h0 h1))

hom² :
  {l : Level} {A : UU l} {x y z : A} →
  hom x y → hom y z → hom x z → UU l
hom² f g h = extension ∂Δ²→Δ² (rec-hom-∂Δ² f g h)

-- hom²-composition :
--   {l : Level} {A : UU l} {x y z : A}
--   (f : hom x y) (g : hom y z) (c : composition f g) → hom² f g (composite-composition f g c)
-- pr1 (hom²-composition f g c) = witness-composition f g c
-- pr2 (hom²-composition f g c) x = {!  !}
```

```text
is-composite-arr :
  {l : Level} {A : UU l} → (f g : arr A) → f 1₂ ＝ g 0₂ → arr A → UU l
is-composite-arr f g p h = is-composite-horn (rec-arr-Λ²₁ f g p) h
```

These definitions are not compatible in the same way as the previous ones, as
the second formulation also requires coherence at the end points.

```text
is-composite :
  {l : Level} {A : UU l} {x y z : A} → hom x y → hom y z → hom x z → UU l
is-composite f g h = Σ (composition f g) (λ c → composite-composition f g c ＝ h)
```
