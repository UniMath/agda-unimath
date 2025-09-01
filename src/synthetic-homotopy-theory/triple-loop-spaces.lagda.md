# Triple loop spaces

```agda
module synthetic-homotopy-theory.triple-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.double-loop-spaces
open import synthetic-homotopy-theory.iterated-loop-spaces
```

</details>

## Idea

A **triple loop space** is a three times
[iterated loop space](synthetic-homotopy-theory.iterated-loop-spaces.md).

## Definition

```agda
module _
  {l : Level}
  where

  Ω³ : Pointed-Type l → Pointed-Type l
  Ω³ A = iterated-loop-space 3 A

  type-Ω³ : {A : UU l} (a : A) → UU l
  type-Ω³ a = Id (refl-Ω² {a = a}) (refl-Ω² {a = a})

  refl-Ω³ : {A : UU l} {a : A} → type-Ω³ a
  refl-Ω³ = refl
```

## Operations

```agda
x-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → type-Ω³ a → type-Ω³ a → type-Ω³ a
x-concat-Ω³ = x-concat-Id³

y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → type-Ω³ a → type-Ω³ a → type-Ω³ a
y-concat-Ω³ = y-concat-Id³

z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} → type-Ω³ a → type-Ω³ a → type-Ω³ a
z-concat-Ω³ = z-concat-Id³

ap-x-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} {α α' β β' : type-Ω³ a}
  (s : α ＝ α') (t : β ＝ β') → x-concat-Ω³ α β ＝ x-concat-Ω³ α' β'
ap-x-concat-Ω³ s t = ap-binary x-concat-Ω³ s t

ap-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} {α α' β β' : type-Ω³ a}
  (s : α ＝ α') (t : β ＝ β') → y-concat-Ω³ α β ＝ y-concat-Ω³ α' β'
ap-y-concat-Ω³ s t = j-concat-Id⁴ s t

ap-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} {α α' β β' : type-Ω³ a}
  (s : α ＝ α') (t : β ＝ β') → z-concat-Ω³ α β ＝ z-concat-Ω³ α' β'
ap-z-concat-Ω³ s t = k-concat-Id⁴ s t
```

## Properties

### The unit laws for the three concatenations on Ω³

```agda
left-unit-law-x-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α : type-Ω³ a) →
  x-concat-Ω³ refl-Ω³ α ＝ α
left-unit-law-x-concat-Ω³ α = left-unit

right-unit-law-x-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α : type-Ω³ a) →
  x-concat-Ω³ α refl-Ω³ ＝ α
right-unit-law-x-concat-Ω³ α = right-unit

left-unit-law-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α : type-Ω³ a) →
  y-concat-Ω³ refl-Ω³ α ＝ α
left-unit-law-y-concat-Ω³ α = left-unit-law-horizontal-concat-Ω²

right-unit-law-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α : type-Ω³ a) →
  y-concat-Ω³ α refl-Ω³ ＝ α
right-unit-law-y-concat-Ω³ α = right-unit-law-horizontal-concat-Ω²

left-unit-law-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α : type-Ω³ a) →
  z-concat-Ω³ refl-Ω³ α ＝ α
left-unit-law-z-concat-Ω³ α =
  ( left-unit-law-z-concat-Id³ α) ∙
  ( ( inv right-unit) ∙
    ( ( inv-nat-htpy (λ ω → compute-left-refl-horizontal-concat-Id² ω) α) ∙
      ( ( inv right-unit) ∙
        ( ( inv-nat-htpy ap-id α) ∙
          ( ap-id α)))))

{-
super-naturality-right-unit :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {α β : p ＝ q} (γ : α ＝ β)
  (u : y ＝ z) →
  Id (ap (λ ω → horizontal-concat-Id² ω (refl {x = u})) γ) {!!}
super-naturality-right-unit α = {!!}
-}

{-
right-unit-law-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α : type-Ω³ a) →
  z-concat-Ω³ α refl-Ω³ ＝ α
right-unit-law-z-concat-Ω³ α =
  ( right-unit-law-z-concat-Id³ α) ∙
  {!!}
-}
{-
  ( ( inv right-unit) ∙
    ( ( inv-nat-htpy (λ ω → compute-right-refl-horizontal-concat-Id² ω) α) ∙
      ( left-unit ∙
        ( ( inv right-unit) ∙
          ( ( inv-nat-htpy
                ( λ z →
                  ( inv right-unit) ∙
                  ( inv-nat-htpy (λ ω → right-unit) z) ∙ ( ap-id z)) α) ∙
            ( ap-id α))))))
-}
```

### The interchange laws for Ω³

```agda
interchange-x-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α β γ δ : type-Ω³ a) →
  Id
    ( y-concat-Ω³ (x-concat-Ω³ α β) (x-concat-Ω³ γ δ))
    ( x-concat-Ω³ (y-concat-Ω³ α γ) (y-concat-Ω³ β δ))
interchange-x-y-concat-Ω³ = interchange-x-y-concat-Id³

interchange-x-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α β γ δ : type-Ω³ a) →
  Id
    ( z-concat-Ω³ (x-concat-Ω³ α β) (x-concat-Ω³ γ δ))
    ( x-concat-Ω³ (z-concat-Ω³ α γ) (z-concat-Ω³ β δ))
interchange-x-z-concat-Ω³ = interchange-x-z-concat-Id³

interchange-y-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α β γ δ : type-Ω³ a) →
  Id
    ( z-concat-Ω³ (y-concat-Ω³ α β) (y-concat-Ω³ γ δ))
    ( y-concat-Ω³ (z-concat-Ω³ α γ) (z-concat-Ω³ β δ))
interchange-y-z-concat-Ω³ α β γ δ =
  inv right-unit ∙ interchange-y-z-concat-Id³ α β γ δ
```

### The Eckmann-Hilton connections in Ω³

```agda
outer-eckmann-hilton-connection-x-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α δ : type-Ω³ a) →
  y-concat-Ω³ α δ ＝ x-concat-Ω³ α δ
outer-eckmann-hilton-connection-x-y-concat-Ω³ α δ =
  ( j-concat-Id⁴
    ( inv (right-unit-law-x-concat-Ω³ α))
    ( inv (left-unit-law-x-concat-Ω³ δ))) ∙
  ( ( interchange-x-y-concat-Ω³ α refl refl δ) ∙
    ( i-concat-Id⁴
      ( right-unit-law-y-concat-Ω³ α)
      ( left-unit-law-y-concat-Ω³ δ)))

inner-eckmann-hilton-connection-x-y-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (β γ : type-Ω³ a) →
  y-concat-Ω³ β γ ＝ x-concat-Ω³ γ β
inner-eckmann-hilton-connection-x-y-concat-Ω³ β γ =
  ( j-concat-Id⁴
    ( inv (left-unit-law-x-concat-Ω³ β))
    ( inv (right-unit-law-x-concat-Ω³ γ))) ∙
  ( ( interchange-x-y-concat-Ω³ refl β γ refl) ∙
    ( i-concat-Id⁴
      ( left-unit-law-y-concat-Ω³ γ)
      ( right-unit-law-y-concat-Ω³ β)))

{-
outer-eckmann-hilton-connection-x-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α δ : type-Ω³ a) →
  z-concat-Ω³ α δ ＝ x-concat-Ω³ α δ
outer-eckmann-hilton-connection-x-z-concat-Ω³ α δ =
  ( k-concat-Id⁴
    ( inv (right-unit-law-x-concat-Ω³ α))
    ( inv (left-unit-law-x-concat-Ω³ δ))) ∙
  ( ( interchange-x-z-concat-Ω³ α refl refl δ) ∙
    ( i-concat-Id⁴
      ( right-unit-law-z-concat-Ω³ α)
      ( left-unit-law-z-concat-Ω³ δ)))
-}

{-
inner-eckmann-hilton-connection-x-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (β γ : type-Ω³ a) →
  z-concat-Ω³ β γ ＝ x-concat-Ω³ γ β
inner-eckmann-hilton-connection-x-z-concat-Ω³ β γ =
  ( k-concat-Id⁴
    ( inv (left-unit-law-x-concat-Ω³ β))
    ( inv (right-unit-law-x-concat-Ω³ γ))) ∙
  ( ( interchange-x-z-concat-Ω³ refl β γ refl) ∙
    ( i-concat-Id⁴
      ( left-unit-law-z-concat-Ω³ γ)
      ( right-unit-law-z-concat-Ω³ β)))
-}

{-
outer-eckmann-hilton-connection-y-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (α δ : type-Ω³ a) →
  z-concat-Ω³ α δ ＝ y-concat-Ω³ α δ
outer-eckmann-hilton-connection-y-z-concat-Ω³ α δ =
  ( k-concat-Id⁴
    ( inv (right-unit-law-y-concat-Ω³ α))
    ( inv (left-unit-law-y-concat-Ω³ δ))) ∙
  ( ( interchange-y-z-concat-Ω³ α refl refl δ) ∙
    ( j-concat-Id⁴
      ( right-unit-law-z-concat-Ω³ α)
      ( left-unit-law-z-concat-Ω³ δ)))
-}

{-
inner-eckmann-hilton-connection-y-z-concat-Ω³ :
  {l : Level} {A : UU l} {a : A} (β γ : type-Ω³ a) →
  z-concat-Ω³ β γ ＝ y-concat-Ω³ γ β
inner-eckmann-hilton-connection-y-z-concat-Ω³ β γ =
  ( k-concat-Id⁴
    ( inv (left-unit-law-y-concat-Ω³ β))
    ( inv (right-unit-law-y-concat-Ω³ γ))) ∙
  ( ( interchange-y-z-concat-Ω³ refl β γ refl) ∙
    ( j-concat-Id⁴
      ( left-unit-law-z-concat-Ω³ γ)
      ( right-unit-law-z-concat-Ω³ β)))
-}
```
