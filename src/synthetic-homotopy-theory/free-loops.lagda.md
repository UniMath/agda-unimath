# Free loops

```agda
module synthetic-homotopy-theory.free-loops where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.constant-type-families
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A **free loop** in a type `X` consists of a point `x : X` and an
[identification](foundation.identity-types.md) `x ＝ x`. The type of free loops
in `X` is [equivalent](foundation-core.equivalences.md) to the type of maps
`𝕊¹ → X`.

## Definitions

### Free loops

```agda
free-loop : {l1 : Level} (X : UU l1) → UU l1
free-loop X = Σ X (λ x → x ＝ x)

module _
  {l1 : Level} {X : UU l1}
  where

  base-free-loop : free-loop X → X
  base-free-loop = pr1

  loop-free-loop : (α : free-loop X) → base-free-loop α ＝ base-free-loop α
  loop-free-loop = pr2
```

### Free dependent loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (P : X → UU l2)
  where

  free-dependent-loop : UU l2
  free-dependent-loop =
    Σ ( P (base-free-loop α)) (λ p₀ → tr P (loop-free-loop α) p₀ ＝ p₀)

  base-free-dependent-loop : free-dependent-loop → P (base-free-loop α)
  base-free-dependent-loop = pr1

  loop-free-dependent-loop :
    (β : free-dependent-loop) →
    ( tr P (loop-free-loop α) (base-free-dependent-loop β)) ＝
    ( base-free-dependent-loop β)
  loop-free-dependent-loop = pr2
```

## Properties

### Characterization of the identity type of the type of free loops

```agda
module _
  {l1 : Level} {X : UU l1}
  where

  Eq-free-loop : (α α' : free-loop X) → UU l1
  Eq-free-loop (pair x α) α' =
    Σ (x ＝ base-free-loop α') (λ p → α ∙ p ＝ p ∙ (loop-free-loop α'))

  refl-Eq-free-loop : (α : free-loop X) → Eq-free-loop α α
  pr1 (refl-Eq-free-loop (pair x α)) = refl
  pr2 (refl-Eq-free-loop (pair x α)) = right-unit

  Eq-eq-free-loop : (α α' : free-loop X) → α ＝ α' → Eq-free-loop α α'
  Eq-eq-free-loop α .α refl = refl-Eq-free-loop α

  abstract
    is-torsorial-Eq-free-loop :
      (α : free-loop X) → is-torsorial (Eq-free-loop α)
    is-torsorial-Eq-free-loop (pair x α) =
      is-torsorial-Eq-structure
        ( is-torsorial-Id x)
        ( pair x refl)
        ( is-contr-is-equiv'
          ( Σ (x ＝ x) (λ α' → α ＝ α'))
          ( tot (λ α' α → right-unit ∙ α))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ α' → is-equiv-concat right-unit α'))
          ( is-torsorial-Id α))

  abstract
    is-equiv-Eq-eq-free-loop :
      (α α' : free-loop X) → is-equiv (Eq-eq-free-loop α α')
    is-equiv-Eq-eq-free-loop α =
      fundamental-theorem-id
        ( is-torsorial-Eq-free-loop α)
        ( Eq-eq-free-loop α)
```

### Characterization of the identity type of free dependent loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (P : X → UU l2)
  where

  Eq-free-dependent-loop : (p p' : free-dependent-loop α P) → UU l2
  Eq-free-dependent-loop (pair y p) p' =
    Σ ( y ＝ base-free-dependent-loop α P p')
      ( λ q →
        ( p ∙ q) ＝
        ( ( ap (tr P (loop-free-loop α)) q) ∙
          ( loop-free-dependent-loop α P p')))

  refl-Eq-free-dependent-loop :
    (p : free-dependent-loop α P) → Eq-free-dependent-loop p p
  pr1 (refl-Eq-free-dependent-loop (pair y p)) = refl
  pr2 (refl-Eq-free-dependent-loop (pair y p)) = right-unit

  Eq-free-dependent-loop-eq :
    ( p p' : free-dependent-loop α P) → p ＝ p' → Eq-free-dependent-loop p p'
  Eq-free-dependent-loop-eq p .p refl = refl-Eq-free-dependent-loop p

  abstract
    is-torsorial-Eq-free-dependent-loop :
      ( p : free-dependent-loop α P) → is-torsorial (Eq-free-dependent-loop p)
    is-torsorial-Eq-free-dependent-loop (pair y p) =
      is-torsorial-Eq-structure
        ( is-torsorial-Id y)
        ( pair y refl)
        ( is-contr-is-equiv'
          ( Σ (tr P (loop-free-loop α) y ＝ y) (λ p' → p ＝ p'))
          ( tot (λ p' α → right-unit ∙ α))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ p' → is-equiv-concat right-unit p'))
          ( is-torsorial-Id p))

  abstract
    is-equiv-Eq-free-dependent-loop-eq :
      (p p' : free-dependent-loop α P) →
      is-equiv (Eq-free-dependent-loop-eq p p')
    is-equiv-Eq-free-dependent-loop-eq p =
      fundamental-theorem-id
        ( is-torsorial-Eq-free-dependent-loop p)
        ( Eq-free-dependent-loop-eq p)

  eq-Eq-free-dependent-loop :
    (p p' : free-dependent-loop α P) →
    Eq-free-dependent-loop p p' → p ＝ p'
  eq-Eq-free-dependent-loop p p' =
    map-inv-is-equiv (is-equiv-Eq-free-dependent-loop-eq p p')
```

### The type of free dependent loops in a constant family of types is equivalent to the type of ordinary free loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (Y : UU l2)
  where

  compute-free-dependent-loop-constant-type-family :
    free-loop Y ≃ free-dependent-loop α (λ x → Y)
  compute-free-dependent-loop-constant-type-family =
    equiv-tot
      ( λ y → equiv-concat (tr-constant-type-family (loop-free-loop α) y) y)

  map-compute-free-dependent-loop-constant-type-family :
    free-loop Y → free-dependent-loop α (λ x → Y)
  map-compute-free-dependent-loop-constant-type-family =
    map-equiv compute-free-dependent-loop-constant-type-family
```
