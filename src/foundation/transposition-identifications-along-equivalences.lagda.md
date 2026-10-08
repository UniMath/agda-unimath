# Transposing identifications along equivalences

```agda
module foundation.transposition-identifications-along-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-identifications
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.whiskering-identifications-concatenation
```

</details>

## Idea

Consider an [equivalence](foundation-core.equivalences.md) `e : A ≃ B` and two
elements `x : A` and `y : B`. The
{{#concept "transposition" Disambiguation="identifications along equivalences" Agda=eq-transpose-equiv}}
is an equivalence of [identity types](foundation-core.identity-types.md)

```text
  (e x ＝ y) ≃ (x ＝ e⁻¹ y).
```

There are two ways of constructing this equivalence. One way uses the fact that
`e⁻¹` is a [section](foundation-core.sections.md) of `e`, from which it follows
that

```text
 (e x ＝ y) ≃ (e x ＝ e e⁻¹ y) ≃ (x ＝ e⁻¹ y).
```

In other words, the transpose of an identification `p : e x ＝ y` along `e` is
the unique identification `q : x ＝ e⁻¹ y` equipped with an identification
witnessing that the triangle

```text
      ap e q
  e x ------> e (e⁻¹ y)
     \       /
    p \     / is-section-map-inv-equiv e y
       \   /
        ∨ ∨
         y
```

commutes. The other way uses the fact that `e⁻¹` is a
[retraction](foundation-core.retractions.md) of `e`, resulting in the
equivalence

```text
 (e x ＝ y) ≃ (e⁻¹ e x ＝ e⁻¹ y) ≃ (x ＝ e⁻¹ y) .
```

These two equivalences are [homotopic](foundation-core.homotopies.md), as is
shown below.

## Definitions

### Transposing equalities along equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  eq-transpose-equiv :
    (x : A) (y : B) → (map-equiv e x ＝ y) ≃ (x ＝ map-inv-equiv e y)
  eq-transpose-equiv x y =
    ( inv-equiv (equiv-ap e x (map-inv-equiv e y))) ∘e
    ( equiv-concat'
      ( map-equiv e x)
      ( inv (is-section-map-inv-equiv e y)))

  map-eq-transpose-equiv :
    {x : A} {y : B} → map-equiv e x ＝ y → x ＝ map-inv-equiv e y
  map-eq-transpose-equiv {x} {y} = map-equiv (eq-transpose-equiv x y)

  map-inv-eq-transpose-equiv :
    {x : A} {y : B} → x ＝ map-inv-equiv e y → map-equiv e x ＝ y
  map-inv-eq-transpose-equiv {x} {y} = map-inv-equiv (eq-transpose-equiv x y)

  eq-transpose-equiv' :
    (x : A) (y : B) → (map-equiv e x ＝ y) ≃ (x ＝ map-inv-equiv e y)
  eq-transpose-equiv' x y =
    ( equiv-concat
      ( inv (is-retraction-map-inv-equiv e x))
      ( map-inv-equiv e y)) ∘e
    ( equiv-ap (inv-equiv e) (map-equiv e x) y)

  map-eq-transpose-equiv' :
    {x : A} {y : B} → map-equiv e x ＝ y → x ＝ map-inv-equiv e y
  map-eq-transpose-equiv' {x} {y} = map-equiv (eq-transpose-equiv' x y)
```

### Transposing identifications of reversed identity types along equivalences

It is sometimes useful to consider identifications `y ＝ e x` instead of
`e x ＝ y`, so we include an inverted equivalence for that as well.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  eq-transpose-equiv-inv :
    (x : A) (y : B) → (y ＝ map-equiv e x) ≃ (map-inv-equiv e y ＝ x)
  eq-transpose-equiv-inv x y =
    ( inv-equiv (equiv-ap e _ _)) ∘e
    ( equiv-concat (is-section-map-inv-equiv e y) _)

  map-eq-transpose-equiv-inv :
    {a : A} {b : B} → b ＝ map-equiv e a → map-inv-equiv e b ＝ a
  map-eq-transpose-equiv-inv {a} {b} = map-equiv (eq-transpose-equiv-inv a b)

  map-inv-eq-transpose-equiv-inv :
    {a : A} {b : B} → map-inv-equiv e b ＝ a → b ＝ map-equiv e a
  map-inv-eq-transpose-equiv-inv {a} {b} =
    map-inv-equiv (eq-transpose-equiv-inv a b)
```

## Properties

### Computing transposition of reflexivity along equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  compute-refl-eq-transpose-equiv :
    {x : A} →
    map-eq-transpose-equiv e refl ＝ inv (is-retraction-map-inv-equiv e x)
  compute-refl-eq-transpose-equiv =
    map-eq-transpose-equiv-inv
      ( equiv-ap e _ (map-inv-equiv e _))
      ( ap inv (coherence-map-inv-equiv e _) ∙
        inv (ap-inv (map-equiv e) _))

  compute-refl-eq-transpose-equiv-inv :
    {x : A} →
    map-eq-transpose-equiv-inv e refl ＝ is-retraction-map-inv-equiv e x
  compute-refl-eq-transpose-equiv-inv {x} =
    map-eq-transpose-equiv-inv
      ( equiv-ap e _ _)
      ( ( right-unit) ∙
        ( coherence-map-inv-equiv e _))
```

### The two definitions of transposing identifications along equivalences are homotopic

We begin by showing that the two equivalences stated above are homotopic.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  compute-map-eq-transpose-equiv :
    {x : A} {y : B} →
    map-eq-transpose-equiv e {x} {y} ~ map-eq-transpose-equiv' e
  compute-map-eq-transpose-equiv {x} refl =
    ( map-eq-transpose-equiv-inv
      ( equiv-ap e x _)
      ( ( ap inv (coherence-map-inv-equiv e x)) ∙
        ( inv (ap-inv (map-equiv e) (is-retraction-map-inv-equiv e x))))) ∙
    ( inv right-unit)
```

### The defining commuting triangles of transposed identifications

Transposed identifications fit in
[commuting triangles](foundation.commuting-triangles-of-identifications.md) with
the original identifications.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  triangle-eq-transpose-equiv :
    {x : A} {y : B} (p : map-equiv e x ＝ y) →
    coherence-triangle-identifications'
      ( p)
      ( is-section-map-inv-equiv e y)
      ( ap (map-equiv e) (map-eq-transpose-equiv e p))
  triangle-eq-transpose-equiv {x} {y} p =
    ( right-whisker-concat
      ( is-section-map-inv-equiv
        ( equiv-ap e x (map-inv-equiv e y))
        ( p ∙ inv (is-section-map-inv-equiv e y)))
      ( is-section-map-inv-equiv e y)) ∙
    ( is-section-inv-concat' (is-section-map-inv-equiv e y) p)

  triangle-eq-transpose-equiv-inv :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    coherence-triangle-identifications'
      ( ap (map-equiv e) (map-eq-transpose-equiv-inv e p))
      ( p)
      ( is-section-map-inv-equiv e y)
  triangle-eq-transpose-equiv-inv {x} {y} p =
    inv
      ( is-section-map-inv-equiv
        ( equiv-ap e _ _)
        ( is-section-map-inv-equiv e y ∙ p))

  triangle-eq-transpose-equiv' :
    {x : A} {y : B} (p : map-equiv e x ＝ y) →
    coherence-triangle-identifications'
      ( ap (map-inv-equiv e) p)
      ( map-eq-transpose-equiv e p)
      ( is-retraction-map-inv-equiv e x)
  triangle-eq-transpose-equiv' {x} refl =
    ( left-whisker-concat
      ( is-retraction-map-inv-equiv e x)
      ( compute-map-eq-transpose-equiv e refl)) ∙
    ( is-section-inv-concat (is-retraction-map-inv-equiv e x) refl)

  triangle-eq-transpose-equiv-inv' :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    coherence-triangle-identifications
      ( map-eq-transpose-equiv-inv e p)
      ( is-retraction-map-inv-equiv e x)
      ( ap (map-inv-equiv e) p)
  triangle-eq-transpose-equiv-inv' {x} refl =
    compute-refl-eq-transpose-equiv-inv e

  right-inverse-eq-transpose-equiv :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    ( ( map-eq-transpose-equiv e (inv p)) ∙
      ( ap (map-inv-equiv e) p ∙ is-retraction-map-inv-equiv e x)) ＝
    ( refl)
  right-inverse-eq-transpose-equiv {x} refl =
    ( right-whisker-concat (compute-refl-eq-transpose-equiv e) _) ∙
    ( left-inv (is-retraction-map-inv-equiv e _))
```

### Transposing concatenated identifications along equivalences

Transposing concatenated identifications into a triangle with a transpose of the
left factor.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  triangle-eq-transpose-equiv-concat :
    {x : A} {y z : B} (p : map-equiv e x ＝ y) (q : y ＝ z) →
    ( map-eq-transpose-equiv e (p ∙ q)) ＝
    ( map-eq-transpose-equiv e p ∙ ap (map-inv-equiv e) q)
  triangle-eq-transpose-equiv-concat refl refl = inv right-unit
```
