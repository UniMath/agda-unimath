# Simple type theories

```agda
{-# OPTIONS --guardedness --allow-unsolved-metas #-}

module type-theories.simple-type-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

Simple type theories are type theories that have no type dependency. The
category of simple type theories is equivalent to the category of multisorted
algebraic theories.

## Definitions

```agda
module simple where

  record system
    {l1 : Level} (l2 : Level) (T : UU l1) : UU (l1 ⊔ lsuc l2)
    where
    coinductive
    field
      element : T → UU l2
      slice : (X : T) → system l2 T

  record fibered-system
    {l1 l2 l3 : Level} (l4 : Level) {T : UU l1} (S : T → UU l2)
    (A : system l3 T) : UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
    where
    coinductive
    field
      element : {X : T} → S X → system.element A X → UU l4
      slice : {X : T} → S X → fibered-system l4 S (system.slice A X)

  record section-system
    {l1 l2 l3 l4 : Level} {T : UU l1} {S : T → UU l2} {A : system l3 T}
    (B : fibered-system l4 S A) (f : (X : T) → S X) : UU (l1 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      element :
        {X : T} (x : system.element A X) → fibered-system.element B (f X) x
      slice :
        (X : T) → section-system (fibered-system.slice B (f X)) f

  ------------------------------------------------------------------------------
```

We will introduce homotopies of sections of fibered systems. However, in order
to define concatenation of those homotopies, we will first define heterogeneous
homotopies of sections of fibered systems.

```agda
  Eq-fibered-system' :
    {l1 l2 l3 l4 : Level} {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B B' : fibered-system l4 S A} (α : B ＝ B') {f f' : (X : T) → S X}
    (g : section-system B f) (g' : section-system B' f') →
    fibered-system l4 (λ t → Id (f t) (f' t)) A
  fibered-system.element (Eq-fibered-system' {B = B} refl {f} g g') {X} p x =
    Id
      ( tr
        ( λ u → fibered-system.element B u x)
        ( p)
        ( section-system.element g x))
      ( section-system.element g' x)
  fibered-system.slice (Eq-fibered-system' {B = B} refl g g') {X} p =
    Eq-fibered-system'
      ( ap (fibered-system.slice B) p)
      ( section-system.slice g X)
      ( section-system.slice g' X)

  htpy-section-system' :
    {l1 l2 l3 l4 : Level} {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B B' : fibered-system l4 S A} (α : B ＝ B') {f f' : (X : T) → S X}
    (H : f ~ f') (g : section-system B f) (g' : section-system B' f') →
    UU (l1 ⊔ l2 ⊔ l4)
  htpy-section-system' α H g g' =
    section-system (Eq-fibered-system' α g g') H

  concat-htpy-section-system' :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B B' B'' : fibered-system l4 S A} {α : B ＝ B'} {β : B' ＝ B''}
    (γ : B ＝ B'') (δ : Id (α ∙ β) γ) {f f' f'' : (X : T) → S X}
    {H : f ~ f'} {H' : f' ~ f''} {g : section-system B f}
    {g' : section-system B' f'} {g'' : section-system B'' f''}
    (K : htpy-section-system' α H g g')
    (K' : htpy-section-system' β H' g' g'') →
    htpy-section-system' γ (H ∙h H') g g''
  section-system.element
    ( concat-htpy-section-system'
      {B = B} {α = refl} {refl} .refl refl {H = H} {H'} {g} K K') {X} x =
    ( tr-concat
      { B = λ t → fibered-system.element B t x}
      ( H X)
      ( H' X)
      ( section-system.element g x)) ∙
    ( ( ap
        ( tr
          ( λ t → fibered-system.element B t x)
          ( H' X))
        ( section-system.element K x)) ∙
      ( section-system.element K' x))
  section-system.slice
    ( concat-htpy-section-system'
      {B = B} {α = refl} {refl} .refl refl {H = H} {H'} K K') X =
    concat-htpy-section-system'
      ( ap (fibered-system.slice B) (H X ∙ H' X))
      ( inv (ap-concat (fibered-system.slice B) (H X) (H' X)))
      ( section-system.slice K X)
      ( section-system.slice K' X)

  inv-htpy-section-system' :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B B' : fibered-system l4 S A}
    {α : B ＝ B'} (β : B' ＝ B) (γ : Id (inv α) β)
    {f f' : (X : T) → S X} {g : section-system B f}
    {g' : section-system B' f'} {H : f ~ f'} →
    htpy-section-system' α H g g' → htpy-section-system' β (inv-htpy H) g' g
  section-system.element
    ( inv-htpy-section-system' {α = refl} .refl refl {H = H} K) {X} x =
    eq-transpose-tr
      ( H X)
      ( inv (section-system.element K x))
  section-system.slice
    ( inv-htpy-section-system' {B = B} {α = refl} .refl refl {H = H} K) X =
    inv-htpy-section-system'
      ( ap (fibered-system.slice B) (inv (H X)))
      ( inv (ap-inv (fibered-system.slice B) (H X)))
      ( section-system.slice K X)
```

### Nonhomogenous homotopies

We specialize the above definitions to nonhomogenous homotopies.

```agda
  htpy-section-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B : fibered-system l4 S A} {f f' : (X : T) → S X} →
    (f ~ f') → section-system B f → section-system B f' → UU (l1 ⊔ l2 ⊔ l4)
  htpy-section-system H g g' = htpy-section-system' refl H g g'

  refl-htpy-section-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B : fibered-system l4 S A} {f : (X : T) → S X}
    (g : section-system B f) → htpy-section-system refl-htpy g g
  section-system.element (refl-htpy-section-system g) = refl-htpy
  section-system.slice (refl-htpy-section-system g) X =
    refl-htpy-section-system (section-system.slice g X)

  concat-htpy-section-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B : fibered-system l4 S A} {f f' f'' : (X : T) → S X}
    {g : section-system B f} {g' : section-system B f'}
    {g'' : section-system B f''} {H : f ~ f'} {H' : f' ~ f''} →
    htpy-section-system H g g' → htpy-section-system H' g' g'' →
    htpy-section-system (H ∙h H') g g''
  concat-htpy-section-system K K' =
    concat-htpy-section-system' refl refl K K'

  inv-htpy-section-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : system l2 T} {S : T → UU l3}
    {B : fibered-system l4 S A} {f f' : (X : T) → S X}
    {g : section-system B f} {g' : section-system B f'} {H : f ~ f'} →
    htpy-section-system H g g' → htpy-section-system (inv-htpy H) g' g
  inv-htpy-section-system K =
    inv-htpy-section-system' refl refl K
```

---

```agda
  constant-fibered-system :
    {l1 l2 l3 l4 : Level} {T : UU l1} (A : system l2 T) {S : UU l3}
    (B : system l4 S) → fibered-system l4 (λ X → S) A
  fibered-system.element (constant-fibered-system A B) Y x = system.element B Y
  fibered-system.slice (constant-fibered-system A B) {X} Y =
    constant-fibered-system
      ( system.slice A X)
      ( system.slice B Y)

  hom-system :
    {l1 l2 l3 l4 : Level} {T : UU l1} {S : UU l2} (f : T → S)
    (A : system l3 T) (B : system l4 S) → UU (l1 ⊔ l3 ⊔ l4)
  hom-system f A B = section-system (constant-fibered-system A B) f

  htpy-hom-system :
    {l1 l2 l3 l4 : Level} {T : UU l1} {S : UU l2} {f : T → S}
    {A : system l3 T} {B : system l4 S} (g h : hom-system f A B) →
    UU (l1 ⊔ l3 ⊔ l4)
  htpy-hom-system g h = htpy-section-system {!!} {!!} {!!}

  id-hom-system :
    {l1 l2 : Level} {T : UU l1} (A : system l2 T) → hom-system id A A
  section-system.element (id-hom-system A) {X} = id
  section-system.slice (id-hom-system A) X = id-hom-system (system.slice A X)

  comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {T : UU l1} {S : UU l2} {R : UU l3} {g : S → R}
    {f : T → S} {A : system l4 T} {B : system l5 S} {C : system l6 R}
    (β : hom-system g B C) (α : hom-system f A B) → hom-system (g ∘ f) A C
  section-system.element (comp-hom-system {f = f} β α) {X} =
    section-system.element β {f X} ∘ section-system.element α {X}
  section-system.slice (comp-hom-system {f = f} β α) X =
    comp-hom-system (section-system.slice β (f X)) (section-system.slice α X)

  record weakening
    {l1 l2 : Level} {T : UU l1} (A : system l2 T) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : T) → hom-system id A (system.slice A X)
      slice : (X : T) → weakening (system.slice A X)

  record preserves-weakening
    {l1 l2 l3 l4 : Level} {T : UU l1} {S : UU l2} {f : T → S}
    {A : system l3 T} {B : system l4 S} (WA : weakening A) (WB : weakening B)
    (h : hom-system f A B) : UU (l1 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      element :
        (X : T) →
        htpy-hom-system
          ( comp-hom-system
            ( section-system.slice h X)
            ( weakening.element WA X))
          ( comp-hom-system
            ( weakening.element WB (f X))
            ( h))
      slice :
        (X : T) →
        preserves-weakening
          ( weakening.slice WA X)
          ( weakening.slice WB (f X))
          ( section-system.slice h X)

  record substitution
    {l1 l2 : Level} {T : UU l1} (A : system l2 T) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element :
        {X : T} (x : system.element A X) →
        hom-system id (system.slice A X) A
      slice :
        (X : T) → substitution (system.slice A X)

  record preserves-substitution
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {S : UU l2} {f : T → S} {A : system l3 T}
    {B : system l4 S} (SA : substitution A) (SB : substitution B)
    (h : hom-system f A B) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      element :
        {X : T} (x : system.element A X) →
        htpy-hom-system
          ( comp-hom-system
            ( h)
            ( substitution.element SA x))
          ( comp-hom-system
            ( substitution.element SB
              ( section-system.element h x))
            ( section-system.slice h X))
      slice :
        (X : T) →
        preserves-substitution
          ( substitution.slice SA X)
          ( substitution.slice SB (f X))
          ( section-system.slice h X)

  record generic-element
    {l1 l2 : Level} {T : UU l1} (A : system l2 T) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      element : (X : T) → system.element (system.slice A X) X
      slice : (X : T) → generic-element (system.slice A X)

  record preserves-generic-element
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {S : UU l2} {f : T → S}
    {A : system l3 T} {B : system l4 S}
    (δA : generic-element A) (δB : generic-element B)
    (h : hom-system f A B) : UU (l1 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      element :
        (X : T) →
        Id
          ( section-system.element
            ( section-system.slice h X)
            ( generic-element.element δA X))
          ( generic-element.element δB (f X))
      slice :
        (X : T) →
        preserves-generic-element
          ( generic-element.slice δA X)
          ( generic-element.slice δB (f X))
          ( section-system.slice h X)

  module _
    {l1 l2 : Level} {T : UU l1}
    where

    record weakening-preserves-weakening
      {A : system l2 T} (W : weakening A) : UU (l1 ⊔ l2)
      where
      coinductive
      field
        element :
          (X : T) →
          preserves-weakening
            ( W)
            ( weakening.slice W X)
            ( weakening.element W X)
        slice :
          (X : T) → weakening-preserves-weakening (weakening.slice W X)

    record substitution-preserves-substitution
      {A : system l2 T} (S : substitution A) : UU (l1 ⊔ l2)
      where
      coinductive
      field
        element :
          {X : T} (x : system.element A X) →
          preserves-substitution
            ( substitution.slice S X)
            ( S)
            ( substitution.element S x)
        slice :
          (X : T) →
          substitution-preserves-substitution (substitution.slice S X)

    record weakening-preserves-substitution
      {A : system l2 T} (W : weakening A) (S : substitution A) : UU (l1 ⊔ l2)
      where
      coinductive
      field
        element :
          (X : T) →
          preserves-substitution
            ( S)
            ( substitution.slice S X)
            ( weakening.element W X)
        slice :
          (X : T) →
          weakening-preserves-substitution
            ( weakening.slice W X)
            ( substitution.slice S X)

    record substitution-preserves-weakening
      {A : system l2 T} (W : weakening A) (S : substitution A) : UU (l1 ⊔ l2)
      where
      coinductive
      field
        element :
          {X : T} (x : system.element A X) →
          preserves-weakening
            ( weakening.slice W X)
            ( W)
            ( substitution.element S x)
        slice :
          (X : T) →
          substitution-preserves-weakening
            ( weakening.slice W X)
            ( substitution.slice S X)

    record weakening-preserves-generic-element
      {A : system l2 T} (W : weakening A) (δ : generic-element A) :
      UU (l1 ⊔ l2)
      where
      coinductive
      field
        element :
          (X : T) →
          preserves-generic-element
            ( δ)
            ( generic-element.slice δ X)
            ( weakening.element W X)
        slice :
          (X : T) →
          weakening-preserves-generic-element
            ( weakening.slice W X)
            ( generic-element.slice δ X)

    record substitution-preserves-generic-element
      {A : system l2 T} (S : substitution A) (δ : generic-element A) :
      UU (l1 ⊔ l2)
      where
      coinductive
      field
        element :
          {X : T} (x : system.element A X) →
          preserves-generic-element
            ( generic-element.slice δ X)
            ( δ)
            ( substitution.element S x)
        slice :
          (X : T) →
          substitution-preserves-generic-element
            ( substitution.slice S X)
            ( generic-element.slice δ X)

    record substitution-cancels-weakening
      {A : system l2 T} (W : weakening A) (S : substitution A) : UU (l1 ⊔ l2)
      where
      coinductive
      field
        element :
          {X : T} (x : system.element A X) →
          htpy-hom-system
            ( comp-hom-system
              ( substitution.element S x)
              ( weakening.element W X))
            ( id-hom-system A)
        slice :
          (X : T) →
          substitution-cancels-weakening
            ( weakening.slice W X)
            ( substitution.slice S X)

    record generic-element-is-identity
      {A : system l2 T} (S : substitution A) (δ : generic-element A) :
      UU (l1 ⊔ l2)
      where
      coinductive
      field
        element :
          {X : T} (x : system.element A X) →
          Id ( section-system.element
                ( substitution.element S x)
                ( generic-element.element δ X))
              ( x)
        slice :
          (X : T) →
          generic-element-is-identity
            ( substitution.slice S X)
            ( generic-element.slice δ X)

    record substitution-by-generic-element
      {A : system l2 T} (W : weakening A) (S : substitution A)
      (δ : generic-element A) : UU (l1 ⊔ l2)
      where
      coinductive
      field
        element :
          (X : T) →
          htpy-hom-system
            ( comp-hom-system
              ( substitution.element
                ( substitution.slice S X)
                ( generic-element.element δ X))
              ( weakening.element (weakening.slice W X) X))
            ( id-hom-system (system.slice A X))
        slice :
          (X : T) →
          substitution-by-generic-element
            ( weakening.slice W X)
            ( substitution.slice S X)
            ( generic-element.slice δ X)

  record type-theory
    (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
    where
    field
      typ : UU l1
      sys : system l2 typ
      W : weakening sys
      S : substitution sys
      δ : generic-element sys
      WW : weakening-preserves-weakening W
      SS : substitution-preserves-substitution S
      WS : weakening-preserves-substitution W S
      SW : substitution-preserves-weakening W S
      Wδ : weakening-preserves-generic-element W δ
      Sδ : substitution-preserves-generic-element S δ
      S!W : substitution-cancels-weakening W S
      δid : generic-element-is-identity S δ
      Sδ! : substitution-by-generic-element W S δ

  slice-type-theory :
    {l1 l2 : Level} (T : type-theory l1 l2)
    (X : type-theory.typ T) →
    type-theory l1 l2
  type-theory.typ (slice-type-theory T X) =
    type-theory.typ T
  type-theory.sys (slice-type-theory T X) =
    system.slice (type-theory.sys T) X
  type-theory.W (slice-type-theory T X) =
    weakening.slice (type-theory.W T) X
  type-theory.S (slice-type-theory T X) =
    substitution.slice (type-theory.S T) X
  type-theory.δ (slice-type-theory T X) =
    generic-element.slice (type-theory.δ T) X
  type-theory.WW (slice-type-theory T X) =
    weakening-preserves-weakening.slice (type-theory.WW T) X
  type-theory.SS (slice-type-theory T X) =
    substitution-preserves-substitution.slice (type-theory.SS T) X
  type-theory.WS (slice-type-theory T X) =
    weakening-preserves-substitution.slice (type-theory.WS T) X
  type-theory.SW (slice-type-theory T X) =
    substitution-preserves-weakening.slice (type-theory.SW T) X
  type-theory.Wδ (slice-type-theory T X) =
    weakening-preserves-generic-element.slice (type-theory.Wδ T) X
  type-theory.Sδ (slice-type-theory T X) =
    substitution-preserves-generic-element.slice (type-theory.Sδ T) X
  type-theory.S!W (slice-type-theory T X) =
    substitution-cancels-weakening.slice (type-theory.S!W T) X
  type-theory.δid (slice-type-theory T X) =
    generic-element-is-identity.slice (type-theory.δid T) X
  type-theory.Sδ! (slice-type-theory T X) =
    substitution-by-generic-element.slice (type-theory.Sδ! T) X

module dependent-simple
  where

  open import type-theories.dependent-type-theories
  open import type-theories.fibered-dependent-type-theories

  system :
    {l1 l2 : Level} {T : UU l1} → simple.system l2 T → dependent.system l1 l2
  dependent.system.type (system {T = T} A) = T
  dependent.system.element (system A) X =
    simple.system.element A X
  dependent.system.slice (system A) X =
    system (simple.system.slice A X)

  fibered-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : simple.system l2 T} {S : T → UU l3} →
    simple.fibered-system l4 S A →
    dependent.fibered-system l3 l4 (system A)
  dependent.fibered-system.type (fibered-system {S = S} B) = S
  dependent.fibered-system.element (fibered-system B) Y =
    simple.fibered-system.element B Y
  dependent.fibered-system.slice (fibered-system B) Y =
    fibered-system (simple.fibered-system.slice B Y)

  section-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : simple.system l2 T} {S : T → UU l3}
    {B : simple.fibered-system l4 S A} {f : (X : T) → S X} →
    simple.section-system B f → dependent.section-system (fibered-system B)
  dependent.section-system.type (section-system {B = B} {f} g) X = f X
  dependent.section-system.element (section-system {B = B} {f} g) x =
    simple.section-system.element g x
  dependent.section-system.slice (section-system {B = B} {f} g) X =
    section-system (simple.section-system.slice g X)

  Eq-fibered-system' :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : simple.system l2 T} {S : T → UU l3}
    {B B' : simple.fibered-system l4 S A} (α : B ＝ B')
    {f f' : (X : T) → S X}
    (g : simple.section-system B f) (g' : simple.section-system B' f') →
    fibered.hom-fibered-system
      ( dependent.id-hom-system (system A))
      ( fibered-system (simple.Eq-fibered-system' α g g'))
      ( dependent.Eq-fibered-system'
        ( ap fibered-system α)
        ( section-system g)
        ( section-system g'))
  fibered.section-fibered-system.type (Eq-fibered-system' refl f g) Y = Y
  fibered.section-fibered-system.element (Eq-fibered-system' refl f g) y = y
  fibered.section-fibered-system.slice (Eq-fibered-system' refl f g) Y =
    {!Eq-fibered-system' ? ? ? !}

  htpy-section-system' :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : simple.system l2 T} {S : T → UU l3}
    {B B' : simple.fibered-system l4 S A} (α : B ＝ B') {f f' : (X : T) → S X}
    {H : f ~ f'} {g : simple.section-system B f}
    {g' : simple.section-system B' f'} → simple.htpy-section-system' α H g g' →
    dependent.htpy-section-system'
      ( ap fibered-system α)
      ( section-system g)
      ( section-system g')
  dependent.section-system.type (htpy-section-system' refl {H = H} K) = H
  dependent.section-system.element (htpy-section-system' refl {H = H} K) =
    simple.section-system.element K
  dependent.section-system.slice (htpy-section-system' refl {H = H} K) X =
    {!htpy-section-system' ? ? !}

  htpy-section-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {A : simple.system l2 T} {S : T → UU l3}
    {B : simple.fibered-system l4 S A} {f f' : (X : T) → S X} {H : f ~ f'}
    {g : simple.section-system B f} {g' : simple.section-system B f'} →
    simple.htpy-section-system H g g' →
    dependent.htpy-section-system (section-system g) (section-system g')
  dependent.section-system.type (htpy-section-system {H = H} K) = H
  dependent.section-system.element (htpy-section-system {H = H} K) =
    simple.section-system.element K
  dependent.section-system.slice (htpy-section-system {H = H} K) X =
    {!htpy-section-system ? !}

  hom-system :
    {l1 l2 l3 l4 : Level} {T : UU l1} {S : UU l3} {f : T → S}
    {A : simple.system l2 T} {B : simple.system l4 S} →
    simple.hom-system f A B →
    dependent.hom-system (system A) (system B)
  dependent.section-system.type (hom-system {f = f} h) = f
  dependent.section-system.element (hom-system h) =
    simple.section-system.element h
  dependent.section-system.slice (hom-system h) X =
    hom-system (simple.section-system.slice h X)

  comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level}
    {T : UU l1} {S : UU l2} {R : UU l3}
    {g : S → R} {f : T → S} {A : simple.system l4 T} {B : simple.system l5 S}
    {C : simple.system l6 R} (k : simple.hom-system g B C)
    (h : simple.hom-system f A B) →
    dependent.htpy-hom-system
      ( hom-system
        ( simple.comp-hom-system k h))
      ( dependent.comp-hom-system
        ( hom-system k)
        ( hom-system h))
  dependent.section-system.type (comp-hom-system k h) X = refl
  dependent.section-system.element (comp-hom-system k h) x = refl
  dependent.section-system.slice (comp-hom-system {f = f} k h) X =
    comp-hom-system
      ( simple.section-system.slice k (f X))
      ( simple.section-system.slice h X)

  htpy-hom-system :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {S : UU l2} {f : T → S}
    {A : simple.system l3 T} {B : simple.system l4 S}
    {g h : simple.hom-system f A B} →
    simple.htpy-hom-system g h →
    dependent.htpy-hom-system (hom-system g) (hom-system h)
  dependent.section-system.type (htpy-hom-system H) = refl-htpy
  dependent.section-system.element (htpy-hom-system {f = f} H) {X} x =
    simple.section-system.element {f = {!!}} H x
    --simple.section-system.element H {X} x
  dependent.section-system.slice (htpy-hom-system H) X =
    {!!} --htpy-hom-system (simple.section-system.slice H X)

  weakening :
    {l1 l2 : Level} {T : UU l1} {A : simple.system l2 T} →
    simple.weakening A → dependent.weakening (system A)
  dependent.weakening.type (weakening W) X =
    hom-system (simple.weakening.element W X)
  dependent.weakening.slice (weakening W) X =
    weakening (simple.weakening.slice W X)

  preserves-weakening :
    {l1 l2 l3 l4 : Level}
    {T : UU l1} {S : UU l2} {f : T → S}
    {A : simple.system l3 T} {B : simple.system l4 S}
    {WA : simple.weakening A} {WB : simple.weakening B}
    {g : simple.hom-system f A B} →
    simple.preserves-weakening WA WB g →
    dependent.preserves-weakening
      ( weakening WA)
      ( weakening WB)
      ( hom-system g)
  dependent.preserves-weakening.type
    ( preserves-weakening {f = f} {WA = WA} {WB} {g = g} Wg) X =
    dependent.concat-htpy-hom-system
      ( dependent.inv-htpy-hom-system
        ( comp-hom-system
          ( simple.section-system.slice g X)
          ( simple.weakening.element WA X)))
      ( dependent.concat-htpy-hom-system
        ( htpy-hom-system (simple.preserves-weakening.element Wg X))
        ( comp-hom-system
          ( simple.weakening.element WB (f X))
          ( g)))
  dependent.preserves-weakening.slice (preserves-weakening Wg) X =
    preserves-weakening (simple.preserves-weakening.slice Wg X)

  substitution :
    {l1 l2 : Level} {T : UU l1} {A : simple.system l2 T} →
    simple.substitution A →
    dependent.substitution (system A)
  dependent.substitution.type
    ( substitution S) x =
    hom-system (simple.substitution.element S x)
  dependent.substitution.slice
    ( substitution S) X =
    substitution (simple.substitution.slice S X)

  generic-element :
    {l1 l2 : Level} {T : UU l1} {A : simple.system l2 T} →
    (W : simple.weakening A) → simple.generic-element A →
    dependent.generic-element (weakening W)
  dependent.generic-element.type
    ( generic-element W δ) X =
    simple.generic-element.element δ X
  dependent.generic-element.slice
    ( generic-element W δ) X =
    generic-element
      ( simple.weakening.slice W X)
      ( simple.generic-element.slice δ X)

  weakening-preserves-weakening :
    {l1 l2 : Level} {T : UU l1} {A : simple.system l2 T}
    {W : simple.weakening A} →
    simple.weakening-preserves-weakening W →
    dependent.weakening-preserves-weakening (weakening W)
  dependent.weakening-preserves-weakening.type
    ( weakening-preserves-weakening WW) X =
    preserves-weakening (simple.weakening-preserves-weakening.element WW X)
  dependent.weakening-preserves-weakening.slice
    ( weakening-preserves-weakening WW) X =
    weakening-preserves-weakening
      ( simple.weakening-preserves-weakening.slice WW X)
```
