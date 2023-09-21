# Factorizations of maps

```agda
module orthogonal-factorization-systems.factorizations-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import orthogonal-factorization-systems.function-classes
```

</details>

## Idea

A **factorization** of a map `f : A → B` is a pair of maps `g : X → B` and
`h : A → X` such that their composite `g ∘ h` is `f`.

```text
       X
      ^ \
   h /   \ g
    /     v
  A -----> B
      f
```

We use diagrammatic order and say the map `h` is the _left_ and `g` the _right_
map of the factorization.

## Definitions

### Factorizations

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-factorization :
    {l3 : Level} {X : UU l3} →
    (g : X → B) (h : A → X) → UU (l1 ⊔ l2)
  is-factorization g h = f ~ (g ∘ h)

  factorization-through : {l3 : Level} (X : UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  factorization-through X =
    Σ ( X → B)
      ( λ g →
        Σ ( A → X)
          ( is-factorization g))

  factorization : (l3 : Level) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  factorization l3 = Σ (UU l3) (factorization-through)
```

### Components of a factorization

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  right-map-factorization-through :
    {l3 : Level} {X : UU l3} → factorization-through f X → X → B
  right-map-factorization-through = pr1

  left-map-factorization-through :
    {l3 : Level} {X : UU l3} → factorization-through f X → A → X
  left-map-factorization-through = pr1 ∘ pr2

  is-factorization-factorization-through :
    {l3 : Level} {X : UU l3} (F : factorization-through f X) →
      is-factorization f
        ( right-map-factorization-through F)
        ( left-map-factorization-through F)
  is-factorization-factorization-through = pr2 ∘ pr2

  type-factorization : {l3 : Level} (F : factorization f l3) → UU l3
  type-factorization = pr1

  factorization-through-factorization :
    {l3 : Level} (F : factorization f l3) →
    factorization-through f (type-factorization F)
  factorization-through-factorization = pr2

  right-map-factorization :
    {l3 : Level} (F : factorization f l3) → type-factorization F → B
  right-map-factorization =
    right-map-factorization-through ∘ factorization-through-factorization

  left-map-factorization :
    {l3 : Level} (F : factorization f l3) → A → type-factorization F
  left-map-factorization =
    left-map-factorization-through ∘ factorization-through-factorization

  is-factorization-factorization :
    {l3 : Level} (F : factorization f l3) →
    is-factorization f (right-map-factorization F) (left-map-factorization F)
  is-factorization-factorization =
    is-factorization-factorization-through ∘ factorization-through-factorization
```

## Factorizations with function classes

```agda
module _
  {l1 l2 lF lL lR : Level}
  (L : function-class l1 lF lL)
  (R : function-class lF l2 lR)
  {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-factorization-function-class-Prop : factorization f lF → Prop (lL ⊔ lR)
  is-factorization-function-class-Prop F =
    conj-Prop (L (left-map-factorization F)) (R (right-map-factorization F))

  is-factorization-function-class : factorization f lF → UU (lL ⊔ lR)
  is-factorization-function-class =
    type-Prop ∘ is-factorization-function-class-Prop

  factorization-function-class :
    UU (l1 ⊔ l2 ⊔ lsuc lF ⊔ lL ⊔ lR)
  factorization-function-class =
    Σ (factorization f lF) (is-factorization-function-class)
```

## Properties

### Characterization of identifications of factorizations through a type

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  {X : UU l3}
  where

  coherence-htpy-factorization-through :
    (F F' : factorization-through f X) →
    right-map-factorization-through F ~ right-map-factorization-through F' →
    left-map-factorization-through F ~ left-map-factorization-through F' →
    UU (l1 ⊔ l2)
  coherence-htpy-factorization-through F F' R L =
    ( is-factorization-factorization-through F ∙h htpy-comp-horizontal L R) ~
    is-factorization-factorization-through F'

  htpy-factorization-through :
    (F F' : factorization-through f X) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-factorization-through F F' =
    Σ ( right-map-factorization-through F ~ right-map-factorization-through F')
      ( λ R →
        Σ ( left-map-factorization-through F ~
            left-map-factorization-through F')
          ( coherence-htpy-factorization-through F F' R))

  refl-htpy-factorization-through :
    (F : factorization-through f X) → htpy-factorization-through F F
  pr1 (refl-htpy-factorization-through F) = refl-htpy
  pr1 (pr2 (refl-htpy-factorization-through F)) = refl-htpy
  pr2 (pr2 (refl-htpy-factorization-through F)) = right-unit-htpy

  htpy-eq-factorization-through :
    (F F' : factorization-through f X) →
    F ＝ F' → htpy-factorization-through F F'
  htpy-eq-factorization-through F .F refl = refl-htpy-factorization-through F

  is-contr-total-htpy-factorization-through :
    (F : factorization-through f X) →
    is-contr (Σ (factorization-through f X) (htpy-factorization-through F))
  is-contr-total-htpy-factorization-through F =
    is-contr-total-Eq-structure
      ( λ g hH R →
        Σ ( left-map-factorization-through F ~
            left-map-factorization-through (g , hH))
          ( coherence-htpy-factorization-through F (g , hH) R))
      ( is-contr-total-htpy (right-map-factorization-through F))
      ( right-map-factorization-through F , refl-htpy)
      ( is-contr-total-Eq-structure
        ( λ h H →
          coherence-htpy-factorization-through
            ( F)
            ( right-map-factorization-through F , h , H)
            ( refl-htpy))
        ( is-contr-total-htpy (left-map-factorization-through F))
        ( left-map-factorization-through F , refl-htpy)
        ( is-contr-total-htpy
          ( is-factorization-factorization-through F ∙h refl-htpy)))

  is-equiv-htpy-eq-factorization-through :
    (F F' : factorization-through f X) →
    is-equiv (htpy-eq-factorization-through F F')
  is-equiv-htpy-eq-factorization-through F =
    fundamental-theorem-id
      ( is-contr-total-htpy-factorization-through F)
      ( htpy-eq-factorization-through F)

  extensionality-factorization-through :
    (F F' : factorization-through f X) →
    (F ＝ F') ≃ (htpy-factorization-through F F')
  pr1 (extensionality-factorization-through F F') =
    htpy-eq-factorization-through F F'
  pr2 (extensionality-factorization-through F F') =
    is-equiv-htpy-eq-factorization-through F F'

  eq-htpy-factorization-through :
    (F F' : factorization-through f X) →
    htpy-factorization-through F F' → F ＝ F'
  eq-htpy-factorization-through F F' =
    map-inv-equiv (extensionality-factorization-through F F')
```
