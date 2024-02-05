# Transposing identifications along equivalences

```agda
module foundation.transposition-identifications-along-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import foundation-core.equivalences
open import foundation-core.homotopies
```

</details>

## Idea

Consider an [equivalence](foundation-core.equivalences.md) `e : A ≃ B` and two
elements `x : A` and `y : B`. The
{{#concept "transposition" Disambiguation="identifications along equivalences" Agda=eq-transpose-equiv}}
is an equivalence

```text
  (e x ＝ y) ≃ (x ＝ e⁻¹ y)
```

of [identity types](foundation-core.identity-types.md). There are two ways of
constructing this equivalence. One way uses the fact that `e⁻¹` is a
[section](foundation-core.sections.md) of `e`, from which it follows that

```text
 (e x ＝ y) ≃ (e x ＝ e e⁻¹ y) ≃ (x ＝ e⁻¹ y).
```

The other way usex the fact that `e⁻¹` is a
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

  inv-map-eq-transpose-equiv :
    {x : A} {y : B} → x ＝ map-inv-equiv e y → map-equiv e x ＝ y
  inv-map-eq-transpose-equiv {x} {y} = map-inv-equiv (eq-transpose-equiv x y)

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

It is sometimes useful to consider identifications `y ＝ e x` instead of
`e x ＝ y`, so we include an inverted equivalence for that as well.

```agda
  eq-transpose-equiv-inv :
    (x : A) (y : B) → (y ＝ map-equiv e x) ≃ (map-inv-equiv e y ＝ x)
  eq-transpose-equiv-inv x y =
    ( equiv-inv x (map-inv-equiv e y)) ∘e
    ( eq-transpose-equiv x y) ∘e
    ( equiv-inv y (map-equiv e x))

  map-eq-transpose-equiv-inv :
    {a : A} {b : B} → b ＝ map-equiv e a → map-inv-equiv e b ＝ a
  map-eq-transpose-equiv-inv {a} {b} = map-equiv (eq-transpose-equiv-inv a b)

  inv-map-eq-transpose-equiv-inv :
    {a : A} {b : B} → map-inv-equiv e b ＝ a → b ＝ map-equiv e a
  inv-map-eq-transpose-equiv-inv {a} {b} =
    map-inv-equiv (eq-transpose-equiv-inv a b)
```

## Properties

### Computation rules for transposing equivalences

We begin by showing that the two equivalences stated above are homotopic.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  htpy-map-eq-transpose-equiv :
    {x : A} {y : B} →
    map-eq-transpose-equiv e {x} {y} ~ map-eq-transpose-equiv' e
  htpy-map-eq-transpose-equiv {x} refl =
    ( map-eq-transpose-equiv-inv
      ( equiv-ap e x _)
      ( ( ap inv (coherence-map-inv-equiv e x)) ∙
        ( inv (ap-inv (map-equiv e) (is-retraction-map-inv-equiv e x))))) ∙
    ( inv right-unit)
```

Transposing a composition of paths fits into a triangle with a transpose of the
left factor.

```agda
  triangle-eq-transpose-equiv-concat :
    {x : A} {y z : B} (p : map-equiv e x ＝ y) (q : y ＝ z) →
    ( map-eq-transpose-equiv e (p ∙ q)) ＝
    ( map-eq-transpose-equiv e p ∙ ap (map-inv-equiv e) q)
  triangle-eq-transpose-equiv-concat refl refl = inv right-unit
```

Transposed identifications fit in
[commuting triangles](foundation.commuting-triangles-of-identifications.md) with
the original identifications.

```agda
  triangle-eq-transpose-equiv :
    {x : A} {y : B} (p : map-equiv e x ＝ y) →
    ( ( ap (map-equiv e) (map-eq-transpose-equiv e p)) ∙
      ( is-section-map-inv-equiv e y)) ＝
    ( p)
  triangle-eq-transpose-equiv {x} {y} p =
    ( right-whisker-concat
      ( is-section-map-inv-equiv
        ( equiv-ap e x (map-inv-equiv e y))
        ( p ∙ inv (is-section-map-inv-equiv e y)))
      ( is-section-map-inv-equiv e y)) ∙
    ( ( assoc
        ( p)
        ( inv (is-section-map-inv-equiv e y))
        ( is-section-map-inv-equiv e y)) ∙
      ( ( left-whisker-concat p
          ( left-inv (is-section-map-inv-equiv e y))) ∙
        ( right-unit)))

  triangle-eq-transpose-equiv-inv :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    ( (is-section-map-inv-equiv e y) ∙ p) ＝
    ( ap (map-equiv e) (map-eq-transpose-equiv-inv e p))
  triangle-eq-transpose-equiv-inv {x} {y} p =
    map-inv-equiv
      ( equiv-ap
        ( equiv-inv (map-equiv e (map-inv-equiv e y)) (map-equiv e x))
        ( (is-section-map-inv-equiv e y) ∙ p)
        ( ap (map-equiv e) (map-eq-transpose-equiv-inv e p)))
      ( ( distributive-inv-concat (is-section-map-inv-equiv e y) p) ∙
        ( ( inv
            ( right-transpose-eq-concat
              ( ap (map-equiv e) (inv (map-eq-transpose-equiv-inv e p)))
              ( is-section-map-inv-equiv e y)
              ( inv p)
              ( ( right-whisker-concat
                  ( ap
                    ( ap (map-equiv e))
                    ( inv-inv
                      ( map-inv-equiv
                        ( equiv-ap e x (map-inv-equiv e y))
                        ( ( inv p) ∙
                          ( inv (is-section-map-inv-equiv e y))))))
                  ( is-section-map-inv-equiv e y)) ∙
                ( triangle-eq-transpose-equiv (inv p))))) ∙
          ( ap-inv (map-equiv e) (map-eq-transpose-equiv-inv e p))))

  triangle-eq-transpose-equiv' :
    {x : A} {y : B} (p : map-equiv e x ＝ y) →
    ( is-retraction-map-inv-equiv e x ∙ map-eq-transpose-equiv e p) ＝
    ( ap (map-inv-equiv e) p)
  triangle-eq-transpose-equiv' {x} refl =
    ( left-whisker-concat
      ( is-retraction-map-inv-equiv e x)
      ( htpy-map-eq-transpose-equiv refl)) ∙
    ( is-section-inv-concat (is-retraction-map-inv-equiv e x) refl)

  triangle-eq-transpose-equiv-inv' :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    ( map-eq-transpose-equiv-inv e p) ＝
    ( ap (map-inv-equiv e) p ∙ is-retraction-map-inv-equiv e x)
  triangle-eq-transpose-equiv-inv' {x} refl =
    inv
      ( right-transpose-eq-concat
        ( is-retraction-map-inv-equiv e x)
        ( map-eq-transpose-equiv e refl)
        ( refl)
        ( triangle-eq-transpose-equiv' refl))

  right-inverse-eq-transpose-equiv :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    ( ( map-eq-transpose-equiv e (inv p)) ∙
      ( ap (map-inv-equiv e) p ∙ is-retraction-map-inv-equiv e x)) ＝
    ( refl)
  right-inverse-eq-transpose-equiv {x} p =
    inv
      ( map-inv-equiv
        ( equiv-left-transpose-eq-concat'
          ( refl)
          ( map-eq-transpose-equiv e (inv p))
          ( ap (map-inv-equiv e) p ∙ is-retraction-map-inv-equiv e x))
        ( right-unit ∙ triangle-eq-transpose-equiv-inv' p))
```
