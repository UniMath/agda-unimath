# Spines

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.spines
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import reflection.erasing-equality

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.cubes I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
open import simplicial-type-theory.inequality-directed-interval-type I

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.induction-principle-pushouts
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.recursion-principle-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The {{#concept "𝑛-spine" Agda=spine}} is the classifying type of chains of
directed edges of length 𝑛.

```text
  0 ---> 1 ----> ... ----> (n-1) ----> n
```

It has the universal property of the iterated
[pushout](synthetic-homotopy-theory.pushouts.md)

```text
               0▵
         1 ---------> Δ¹
         |            |
  target |            |
         ∨          ⌜ ∨
     spine n ----> spine (n + 1)
```

where

```text
  spine 0 := 1.
```

## Postulates

### The type of 𝑛-spines

> TODO Reconsider this definition.

```agda
postulate
  spine : ℕ → UU I1

  star-spine-0 : spine 0

  contraction-star-spine-0 : (x : spine 0) → star-spine-0 ＝ x

  inl-spine : {n : ℕ} → spine n → spine (succ-ℕ n)

  in-arrow-spine : {n : ℕ} → Δ¹ → spine (succ-ℕ n)

is-contr-spine-0 : is-contr (spine 0)
is-contr-spine-0 = (star-spine-0 , contraction-star-spine-0)

initial-point-spine : (n : ℕ) → spine n
initial-point-spine zero-ℕ = star-spine-0
initial-point-spine (succ-ℕ n) = inl-spine (initial-point-spine n)

terminal-point-spine : (n : ℕ) → spine n
terminal-point-spine zero-ℕ = star-spine-0
terminal-point-spine (succ-ℕ n) = in-arrow-spine 1▵

postulate
  glue-spine :
    {n : ℕ} → inl-spine (terminal-point-spine n) ＝ in-arrow-spine {n} 0▵
```

### The induction principle of the (𝑛+1)-spine

We postulate that the (𝑛+1)-spine is the pushout

```text
               0▵
         1 ---------> Δ¹
         |            |
  target |            |
         ∨          ⌜ ∨
     spine n -----> spine (n + 1)
```

```agda
cocone-spine :
  (n : ℕ) →
  cocone (point (terminal-point-spine n)) (point 0▵) (spine (succ-ℕ n))
cocone-spine n = (inl-spine , in-arrow-spine , point glue-spine)

module _
  {l : Level} (n : ℕ) (P : spine (succ-ℕ n) → UU l)
  (d :
    dependent-cocone
      ( point (terminal-point-spine n))
      ( point 0▵)
      ( cocone-spine n)
      ( P))
  where

  postulate
    dependent-cogap-spine : (x : spine (succ-ℕ n)) → P x

  compute-inl-dependent-cogap-spine :
    (x : spine n) →
    dependent-cogap-spine (inl-spine x) ＝
    horizontal-map-dependent-cocone
      ( point (terminal-point-spine n))
      ( point 0▵)
      ( cocone-spine n)
      ( P)
      ( d)
      ( x)
  compute-inl-dependent-cogap-spine x =
    primEraseEquality compute-inl-dependent-cogap-spine'
    where
    postulate
      compute-inl-dependent-cogap-spine' :
        dependent-cogap-spine (inl-spine x) ＝
        horizontal-map-dependent-cocone
          ( point (terminal-point-spine n))
          ( point 0▵)
          ( cocone-spine n)
          ( P)
          ( d)
          ( x)

  compute-inr-dependent-cogap-spine :
    (t : Δ¹) →
    dependent-cogap-spine (in-arrow-spine t) ＝
    vertical-map-dependent-cocone
      ( point (terminal-point-spine n))
      ( point 0▵)
      ( cocone-spine n)
      ( P)
      ( d)
      ( t)
  compute-inr-dependent-cogap-spine t =
    primEraseEquality compute-inr-dependent-cogap-spine'
    where
    postulate
      compute-inr-dependent-cogap-spine' :
        dependent-cogap-spine (in-arrow-spine t) ＝
        vertical-map-dependent-cocone
          ( point (terminal-point-spine n))
          ( point 0▵)
          ( cocone-spine n)
          ( P)
          ( d)
          ( t)

  postulate
    compute-glue-dependent-cogap-spine :
      coherence-htpy-dependent-cocone
        ( point (terminal-point-spine n))
        ( point 0▵)
        ( cocone-spine n)
        ( P)
        ( dependent-cocone-map
          ( point (terminal-point-spine n))
          ( point 0▵)
          ( cocone-spine n)
          ( P)
          ( dependent-cogap-spine))
        ( d)
        ( compute-inl-dependent-cogap-spine)
        ( compute-inr-dependent-cogap-spine)
```

## Definitions

### The spines as subtypes of the cubes

We can inductively define the 𝑛-spine as a subtype of the 𝑛-cube via t

```text
                 · ┄┄┄┄┄┄> ∙
                ∧∧        ∧∧
              ⋰  ┆      /  ┆
            · ┄┄┄┄┄┄> ∙    ┆
  y   x     ∧    · ┄┄ ∧ ┄> ·
  ∧ ∧       ┆   ∧     |   ∧
  |/        ┆ ⋰       | ⋰
  └-> z     ∙ ------> ∙
```

```agda
subtype-spine : (n : ℕ) → subtype I1 (directed-cube n)
subtype-spine 0 _ = raise-unit-Prop I1
subtype-spine 1 _ = raise-unit-Prop I1
subtype-spine 2 (x , y) = join-Prop (Id-Δ¹-Prop x 1▵) (Id-Δ¹-Prop y 0▵)
subtype-spine (succ-ℕ (succ-ℕ (succ-ℕ n))) (x , u) =
  join-Prop
    ( is-terminal-element-directed-cube-Prop (succ-ℕ (succ-ℕ n)) u)
    ( (Id-Δ¹-Prop x 0▵) ∧ (subtype-spine (succ-ℕ (succ-ℕ n)) u))
```

Let us work out what this definition unfolds to when `n` is `2`:

```text
  subtype-spine 2 (s , t)
  ≐ is-terminal t ∨ ((s ＝ 0▵) ∧ (subtype-spine 1 t))
  ≐ (t ＝ 1▵) ∨ ((s ＝ 0▵) ∧ unit)
  ≃ (t ＝ 1▵) ∨ (s ＝ 0▵).
```

Observe again that the coordinates are read in order from right to left.

```agda
spine' : ℕ → UU I1
spine' n = type-subtype (subtype-spine n)

is-set-spine' : (n : ℕ) → is-set (spine' n)
is-set-spine' n =
  is-set-type-subtype (subtype-spine n) (is-set-directed-cube n)
```

### The point inclusions of the spines

The 𝑛-spine has 𝑛+1 points that we enumerate

```text
  0 ---> 1 ---> 2 ---> ⋯ ---> n
```

```agda
point-spine : (n : ℕ) → Fin (succ-ℕ n) → spine n
point-spine zero-ℕ _ = star-spine-0
point-spine (succ-ℕ n) (inl x) = inl-spine (point-spine n x)
point-spine (succ-ℕ n) (inr x) = terminal-point-spine (succ-ℕ n)

compute-inr-point-spine :
  (n : ℕ) {x : unit} → point-spine n (inr x) ＝ terminal-point-spine n
compute-inr-point-spine zero-ℕ = refl
compute-inr-point-spine (succ-ℕ n) = refl
```

### The arrow inclusions of the spine

The 𝑛-spine has 𝑛 arrows.

```agda
arrow-spine : (n : ℕ) → Fin n → Δ¹ → spine n
arrow-spine (succ-ℕ n) (inl x) = inl-spine ∘ arrow-spine n x
arrow-spine (succ-ℕ n) (inr x) = in-arrow-spine
```

### The hom inclusions of the spine

```agda
source-hom-spine : (n : ℕ) (x : Fin n) → spine n
source-hom-spine n x = point-spine n (inl-Fin n x)

target-hom-spine : (n : ℕ) (x : Fin n) → spine n
target-hom-spine n x = point-spine n (inr-Fin n x)

inv-eq-source-arrow-spine :
  (n : ℕ) (x : Fin n) → source-hom-spine n x ＝ arrow-spine n x 0▵
inv-eq-source-arrow-spine (succ-ℕ n) (inl x) =
  ap inl-spine (inv-eq-source-arrow-spine n x)
inv-eq-source-arrow-spine (succ-ℕ n) (inr x) =
  ap inl-spine (compute-inr-point-spine n) ∙ glue-spine

eq-source-arrow-spine :
  (n : ℕ) (x : Fin n) → arrow-spine n x 0▵ ＝ source-hom-spine n x
eq-source-arrow-spine n x = inv (inv-eq-source-arrow-spine n x)

eq-target-arrow-spine :
  (n : ℕ) (x : Fin n) → arrow-spine n x 1▵ ＝ target-hom-spine n x
eq-target-arrow-spine (succ-ℕ n) (inl x) =
  ap inl-spine (eq-target-arrow-spine n x)
eq-target-arrow-spine (succ-ℕ n) (inr x) = refl

hom-spine : (n : ℕ) (x : Fin n) → source-hom-spine n x →▵ target-hom-spine n x
hom-spine n x =
  ( arrow-spine n x , eq-source-arrow-spine n x , eq-target-arrow-spine n x)
```

### The dependent universal property of the spines

```agda
module _
  (n : ℕ) {l : Level} (P : spine (succ-ℕ n) → UU l)
  where

  htpy-compute-dependent-cogap-spine :
    ( c :
      dependent-cocone
        ( point (terminal-point-spine n))
        ( point 0▵)
        ( cocone-spine n)
        ( P)) →
    htpy-dependent-cocone
      ( point (terminal-point-spine n))
      ( point 0▵)
      ( cocone-spine n)
      ( P)
      ( dependent-cocone-map
        ( point (terminal-point-spine n))
        ( point 0▵)
        ( cocone-spine n)
        ( P)
        ( dependent-cogap-spine n P c))
      ( c)
  htpy-compute-dependent-cogap-spine c =
    ( compute-inl-dependent-cogap-spine n P c ,
      compute-inr-dependent-cogap-spine n P c ,
      compute-glue-dependent-cogap-spine n P c)

  is-section-dependent-cogap-spine :
    is-section
      ( dependent-cocone-map
        ( point (terminal-point-spine n))
        ( point 0▵)
        ( cocone-spine n)
        ( P))
      ( dependent-cogap-spine n P)
  is-section-dependent-cogap-spine c =
    eq-htpy-dependent-cocone
      ( point (terminal-point-spine n))
      ( point 0▵)
      ( cocone-spine n)
      ( P)
      ( dependent-cocone-map
        ( point (terminal-point-spine n))
        ( point 0▵)
        ( cocone-spine n)
        ( P)
        ( dependent-cogap-spine n P c))
      ( c)
      ( htpy-compute-dependent-cogap-spine c)

induction-principle-spine :
  (n : ℕ) →
  induction-principle-pushout
    ( point (terminal-point-spine n))
    ( point 0▵)
    ( cocone-spine n)
induction-principle-spine n P =
  ( dependent-cogap-spine n P , is-section-dependent-cogap-spine n P)

is-retraction-dependent-cogap-spine :
  (n : ℕ) {l : Level} (P : spine (succ-ℕ n) → UU l) →
  is-retraction
    ( dependent-cocone-map
      ( point (terminal-point-spine n))
      ( point 0▵)
      ( cocone-spine n)
      ( P))
    ( dependent-cogap-spine n P)
is-retraction-dependent-cogap-spine n =
  is-retraction-ind-induction-principle-pushout
    ( point (terminal-point-spine n))
    ( point 0▵)
    ( cocone-spine n)
    ( induction-principle-spine n)

dependent-universal-property-spine :
  (n : ℕ) →
  dependent-universal-property-pushout
    ( point (terminal-point-spine n))
    ( point 0▵)
    ( cocone-spine n)
dependent-universal-property-spine n P =
  is-equiv-is-invertible
    ( dependent-cogap-spine n P)
    ( is-section-dependent-cogap-spine n P)
    ( is-retraction-dependent-cogap-spine n P)

equiv-dependent-universal-property-spine :
  (n : ℕ) {l : Level} (P : spine (succ-ℕ n) → UU l) →
  ( (x : spine (succ-ℕ n)) → P x) ≃
  ( dependent-cocone
    ( point (terminal-point-spine n))
    ( point 0▵)
    ( cocone-spine n)
    ( P))
pr1 (equiv-dependent-universal-property-spine n P) =
  dependent-cocone-map
    ( point (terminal-point-spine n))
    ( point 0▵)
    ( cocone-spine n)
    ( P)
pr2 (equiv-dependent-universal-property-spine n P) =
  dependent-universal-property-spine n P
```

### The universal property of the spines

```agda
module _
  (n : ℕ) {l : Level} {X : UU l}
  where

  cogap-spine :
    cocone (point (terminal-point-spine n)) (point 0▵) X → spine (succ-ℕ n) → X
  cogap-spine =
    dependent-cogap-spine n (λ _ → X) ∘
    dependent-cocone-constant-type-family-cocone
      ( point (terminal-point-spine n))
      ( point 0▵)
      ( cocone-spine n)

  is-section-cogap-spine :
    is-section
      ( cocone-map
        ( point (terminal-point-spine n))
        ( point 0▵)
        ( cocone-spine n))
      ( cogap-spine)
  is-section-cogap-spine =
    ( ( triangle-dependent-cocone-map-constant-type-family'
        ( point (terminal-point-spine n))
        ( point 0▵)
        ( cocone-spine n)) ·r
      ( cogap-spine)) ∙h
    ( ( cocone-dependent-cocone-constant-type-family
        ( point (terminal-point-spine n))
        ( point 0▵)
        ( cocone-spine n)) ·l
      ( is-section-dependent-cogap-spine n (λ _ → X)) ·r
      ( dependent-cocone-constant-type-family-cocone
        ( point (terminal-point-spine n))
        ( point 0▵)
        ( cocone-spine n))) ∙h
    ( is-retraction-cocone-dependent-cocone-constant-type-family
      ( point (terminal-point-spine n))
      ( point 0▵)
      ( cocone-spine n))

  is-retraction-cogap-spine :
    is-retraction
      ( cocone-map
        ( point (terminal-point-spine n))
        ( point 0▵)
        ( cocone-spine n))
      ( cogap-spine)
  is-retraction-cogap-spine =
    ( ( cogap-spine) ·l
      ( triangle-dependent-cocone-map-constant-type-family'
        ( point (terminal-point-spine n))
        ( point 0▵)
        ( cocone-spine n))) ∙h
    ( ( dependent-cogap-spine n (λ _ → X)) ·l
      ( is-section-cocone-dependent-cocone-constant-type-family
        ( point (terminal-point-spine n))
        ( point 0▵)
        ( cocone-spine n)) ·r
      ( dependent-cocone-map
        ( point (terminal-point-spine n))
        ( point 0▵)
        ( cocone-spine n)
        ( λ _ → X))) ∙h
    ( is-retraction-dependent-cogap-spine n (λ _ → X))

recursion-principle-spine :
  (n : ℕ) →
  recursion-principle-pushout
    ( point (terminal-point-spine n))
    ( point 0▵)
    ( cocone-spine n)
recursion-principle-spine n = (cogap-spine n , is-section-cogap-spine n)

universal-property-spine :
  (n : ℕ) →
  universal-property-pushout
    ( point (terminal-point-spine n))
    ( point 0▵)
    ( cocone-spine n)
universal-property-spine n Y =
  is-equiv-is-invertible
    ( cogap-spine n)
    ( is-section-cogap-spine n)
    ( is-retraction-cogap-spine n)

equiv-universal-property-spine :
  (n : ℕ) {l : Level} {X : UU l} →
  (spine (succ-ℕ n) → X) ≃ cocone (point (terminal-point-spine n)) (point 0▵) X
equiv-universal-property-spine n {X = X} =
  ( cocone-map (point (terminal-point-spine n)) (point 0▵) (cocone-spine n) ,
    universal-property-spine n X)
```

### Auxiliary definitions for the 𝑛-spine as a subtype of the 𝑛-cube

> This remains to be formalized.

```text
inl-spine' : (n : ℕ) → spine' n → spine' (succ-ℕ n)
inl-spine' zero-ℕ _ = (0▵ , star)
inl-spine' (succ-ℕ zero-ℕ) (t , _) = ((0▵ , t) , inr-join (refl , star))
inl-spine' (succ-ℕ (succ-ℕ n)) x = ((0▵ , {!   !}) , inr-join (refl , {!   !}))

terminal-point-spine' : (n : ℕ) → spine' n
terminal-point-spine' zero-ℕ = star , star
terminal-point-spine' (succ-ℕ zero-ℕ) = 1▵ , star
terminal-point-spine' (succ-ℕ (succ-ℕ n)) = ({!   !} , {!   !})

cocone-spine' :
  (n : ℕ) →
  cocone (point (terminal-point-spine' n)) (point 0▵) (spine' (succ-ℕ n))
cocone-spine' = {!   !}

-- map-spine-spine' :
--   (n : ℕ) → spine' n → spine n
-- map-spine-spine' 0 x = star-spine-0
-- map-spine-spine' 1 (x , u) = in-arrow-spine x
-- map-spine-spine' (succ-ℕ (succ-ℕ n)) ((t , x) , u) =
--   cogap-join
--     ( spine (succ-ℕ (succ-ℕ n)))
--     ( ( λ _ → in-arrow-spine t) ,
--       ( λ rs →
--         inl-spine (map-spine-spine' (succ-ℕ n) (x , pr2 rs))) ,
--       ( λ (is-terminal-x , t=0 , s) →
--         ( ( ap in-arrow-spine t=0) ∙
--           ( inv glue-spine) ∙
--           ( ap inl-spine
--             ( compute-inr-map-spine-spine' n (x , s) is-terminal-x)))))
--     ( u)
--   where
--     compute-inr-map-spine-spine' :
--       (n : ℕ) (xs : spine' (succ-ℕ n)) →
--       is-terminal-element-directed-cube (succ-ℕ n) (pr1 xs) →
--       in-arrow-spine 1▵ ＝ map-spine-spine' (succ-ℕ n) xs
--     compute-inr-map-spine-spine' zero-ℕ xs is-terminal-x =
--       ap in-arrow-spine (inv is-terminal-x)
--     compute-inr-map-spine-spine' (succ-ℕ n) xs is-terminal-x =
--       inv (compute-inl-cogap-join {!   !} {!   !}) ∙ {!   !}

--   -- where map-spine-spine' (succ-ℕ n) (x , s)
```

## Properties

### The 1-spine is the directed interval

```text
      1 ----------> Δ¹
      |             |
    ~ |             | ~
      ∨           ⌜ ∨
   spine 0 ----> spine 1
```

> This remains to be formalized.
