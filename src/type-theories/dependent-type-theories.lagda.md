# Dependent type theories

```agda
{-# OPTIONS --guardedness #-}

module type-theories.dependent-type-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation
```

</details>

## Idea

We introduce the category of dependent type theories, following Voevodsky's
notion of $B$-systems. The category of generalized algebraic theories is defined
to be this category. It should be equivalent to the category of essentially
algebraic theories.

## (Dependency) systems

(Dependency) systems are the structure around which a dependent type theory is
built.

```text
    Ã₀       Ã₁       Ã₂
    |        |        |
    |        |        |
    ∨        ∨        ∨
    A₀ <---- A₁ <---- A₂ <---- ⋯
```

```agda
module dependent where

  record system (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2) where
    coinductive
    field
      type : UU l1
      element : type → UU l2
      slice : (X : type) → system l1 l2

  record fibered-system
    {l1 l2 : Level} (l3 l4 : Level) (A : system l1 l2) :
    UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
    where
    coinductive
    field
      type : system.type A → UU l3
      element : {X : system.type A} → type X → system.element A X → UU l4
      slice : {X : system.type A} → type X →
                fibered-system l3 l4 (system.slice A X)

  record section-system
    {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type : (X : system.type A) → fibered-system.type B X
      element : {X : system.type A} (x : system.element A X) →
                fibered-system.element B (type X) x
      slice : (X : system.type A) →
                section-system (fibered-system.slice B (type X))
```

### Heterogeneous homotopies of sections of fibered systems

will introduce homotopies of sections of fibered systems. However, in order to
define concatenation of those homotopies, we will first define heterogeneous
homotopies of sections of fibered systems.

```agda
  tr-fibered-system-slice :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' : fibered-system l3 l4 A}
    (α : B ＝ B') (f : section-system B) (X : system.type A) →
    Id
      ( fibered-system.slice B (section-system.type f X))
      ( fibered-system.slice B'
        ( section-system.type (tr section-system α f) X))
  tr-fibered-system-slice refl f X = refl

  Eq-fibered-system' :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' : fibered-system l3 l4 A}
    (α : B ＝ B') (f : section-system B) (g : section-system B') →
    fibered-system l3 l4 A
  fibered-system.type (Eq-fibered-system' {A = A} α f g) X =
    Id
      ( section-system.type (tr section-system α f) X)
      ( section-system.type g X)
  fibered-system.element (Eq-fibered-system' {A = A} {B} {B'} α f g) p x =
    Id
      ( tr
        ( λ t → fibered-system.element B' t x)
        ( p)
        ( section-system.element (tr section-system α f) x))
      ( section-system.element g x)
  fibered-system.slice (Eq-fibered-system' {A = A} {B} {B'} α f g) {X} p =
    Eq-fibered-system'
      ( tr-fibered-system-slice α f X ∙ ap (fibered-system.slice B') p)
      ( section-system.slice f X)
      ( section-system.slice g X)

  htpy-section-system' :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' : fibered-system l3 l4 A}
    (α : B ＝ B') (f : section-system B) (g : section-system B') →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-section-system' {A = A} α f g =
    section-system (Eq-fibered-system' α f g)

  concat-htpy-section-system' :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' B'' : fibered-system l3 l4 A}
    {α : B ＝ B'} {β : B' ＝ B''} (γ : B ＝ B'') (δ : Id (α ∙ β) γ)
    {f : section-system B} {g : section-system B'}
    {h : section-system B''}
    (G : htpy-section-system' α f g) (H : htpy-section-system' β g h) →
    htpy-section-system' γ f h
  section-system.type
    ( concat-htpy-section-system' {α = refl} {refl} refl refl G H) =
    section-system.type G ∙h section-system.type H
  section-system.element
    ( concat-htpy-section-system'
      {B = B} {α = refl} {refl} refl refl {f} G H) {X} x =
    ( tr-concat
      { B = λ t → fibered-system.element B t x}
      ( section-system.type G X)
      ( section-system.type H X)
      ( section-system.element f x)) ∙
    ( ( ap
        ( tr
          ( λ t → fibered-system.element B t x)
          ( section-system.type H X))
        ( section-system.element G x)) ∙
      ( section-system.element H x))
  section-system.slice
    ( concat-htpy-section-system' {B = B} {α = refl} {refl} refl refl G H) X =
    concat-htpy-section-system'
      ( ap
        ( fibered-system.slice B)
        ( section-system.type G X ∙ section-system.type H X))
      ( inv
        ( ap-concat
          ( fibered-system.slice B)
          ( section-system.type G X)
          ( section-system.type H X)))
      ( section-system.slice G X)
      ( section-system.slice H X)

  inv-htpy-section-system' :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' : fibered-system l3 l4 A}
    {α : B ＝ B'} (β : B' ＝ B) (γ : Id (inv α) β)
    {f : section-system B} {g : section-system B'} →
    htpy-section-system' α f g → htpy-section-system' β g f
  section-system.type (inv-htpy-section-system' {α = refl} .refl refl H) X =
    inv (section-system.type H X)
  section-system.element
    ( inv-htpy-section-system' {α = refl} .refl refl H) {X} x =
    eq-transpose-tr
      ( section-system.type H X)
      ( inv (section-system.element H x))
  section-system.slice
    ( inv-htpy-section-system' {B = B} {α = refl} .refl refl H) X =
    inv-htpy-section-system'
      ( ap (fibered-system.slice B) (inv (section-system.type H X)))
      ( inv (ap-inv (fibered-system.slice B) (section-system.type H X)))
      ( section-system.slice H X)
```

### Nonhomogenous homotopies

We specialize the above definitions to nonhomogenous homotopies.

```agda
  htpy-section-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    (f g : section-system B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-section-system {A = A} {B} f g =
    htpy-section-system' refl f g

  refl-htpy-section-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    (f : section-system B) → htpy-section-system f f
  section-system.type (refl-htpy-section-system f) X = refl
  section-system.element (refl-htpy-section-system f) x = refl
  section-system.slice (refl-htpy-section-system f) X =
    refl-htpy-section-system (section-system.slice f X)

  concat-htpy-section-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    {f g h : section-system B} (G : htpy-section-system f g)
    (H : htpy-section-system g h) → htpy-section-system f h
  concat-htpy-section-system G H =
    concat-htpy-section-system' refl refl G H

  inv-htpy-section-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    {f g : section-system B} (H : htpy-section-system f g) →
    htpy-section-system g f
  inv-htpy-section-system H = inv-htpy-section-system' refl refl H
```

### Total system of a fibered dependency system

```agda
  total-system :
    {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : fibered-system l3 l4 A) →
    system (l1 ⊔ l3) (l2 ⊔ l4)
  system.type (total-system A B) =
    Σ (system.type A) (fibered-system.type B)
  system.element (total-system A B) (pair X Y) =
    Σ (system.element A X) (fibered-system.element B Y)
  system.slice (total-system A B) (pair X Y) =
    total-system (system.slice A X) (fibered-system.slice B Y)
```

### Morphisms of systems

```agda
  constant-fibered-system :
    {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4) →
    fibered-system l3 l4 A
  fibered-system.type (constant-fibered-system A B) X = system.type B
  fibered-system.element (constant-fibered-system A B) Y x =
    system.element B Y
  fibered-system.slice (constant-fibered-system A B) {X} Y =
    constant-fibered-system (system.slice A X) (system.slice B Y)

  hom-system :
    {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-system A B =
    section-system (constant-fibered-system A B)
```

### Homotopies of morphisms of systems

Homotopies of morphisms of systems are defined as an instance of homotopies of
sections of fibered systems.

```agda
  htpy-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (f g : hom-system A B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-system f g = htpy-section-system f g

  refl-htpy-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (f : hom-system A B) → htpy-hom-system f f
  refl-htpy-hom-system f =
    refl-htpy-section-system f

  concat-htpy-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    {f g h : hom-system A B} →
    htpy-hom-system f g → htpy-hom-system g h → htpy-hom-system f h
  concat-htpy-hom-system G H =
    concat-htpy-section-system G H

  inv-htpy-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    {f g : hom-system A B} → htpy-hom-system f g → htpy-hom-system g f
  inv-htpy-hom-system H = inv-htpy-section-system H
```

## The category of systems

We show that systems form a category.

```agda
  id-hom-system :
    {l1 l2 : Level} (A : system l1 l2) → hom-system A A
  section-system.type (id-hom-system A) X = X
  section-system.element (id-hom-system A) x = x
  section-system.slice (id-hom-system A) X = id-hom-system (system.slice A X)

  comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level}
    {A : system l1 l2} {B : system l3 l4} {C : system l5 l6}
    (g : hom-system B C) (f : hom-system A B) → hom-system A C
  section-system.type (comp-hom-system g f) =
    section-system.type g ∘ section-system.type f
  section-system.element (comp-hom-system g f) =
    ( section-system.element g) ∘ (section-system.element f)
  section-system.slice (comp-hom-system g f) X =
    comp-hom-system
      ( section-system.slice g (section-system.type f X))
      ( section-system.slice f X)

  left-unit-law-comp-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (f : hom-system A B) →
    htpy-hom-system (comp-hom-system (id-hom-system B) f) f
  section-system.type (left-unit-law-comp-hom-system f) = refl-htpy
  section-system.element (left-unit-law-comp-hom-system f) = refl-htpy
  section-system.slice (left-unit-law-comp-hom-system f) X =
    left-unit-law-comp-hom-system (section-system.slice f X)

  right-unit-law-comp-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (f : hom-system A B) →
    htpy-hom-system (comp-hom-system f (id-hom-system A)) f
  section-system.type (right-unit-law-comp-hom-system f) = refl-htpy
  section-system.element (right-unit-law-comp-hom-system f) = refl-htpy
  section-system.slice (right-unit-law-comp-hom-system f) X =
    right-unit-law-comp-hom-system (section-system.slice f X)

  associative-comp-hom-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2} {B : system l3 l4}
    {C : system l5 l6} {D : system l7 l8} (h : hom-system C D)
    (g : hom-system B C) (f : hom-system A B) →
    htpy-hom-system
      ( comp-hom-system (comp-hom-system h g) f)
      ( comp-hom-system h (comp-hom-system g f))
  section-system.type (associative-comp-hom-system h g f) = refl-htpy
  section-system.element (associative-comp-hom-system h g f) = refl-htpy
  section-system.slice (associative-comp-hom-system h g f) X =
    associative-comp-hom-system
      ( section-system.slice h
        ( section-system.type g (section-system.type f X)))
      ( section-system.slice g ( section-system.type f X))
      ( section-system.slice f X)

  left-whisker-comp-hom-system' :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B B' : system l3 l4}
    {C C' : system l5 l6} {g : hom-system B C} {g' : hom-system B' C'}
    (p : B ＝ B')
    {p' : Id (constant-fibered-system A B) (constant-fibered-system A B')}
    (α : Id (ap (constant-fibered-system A) p) p')
    (q : C ＝ C')
    {q' : Id (constant-fibered-system A C) (constant-fibered-system A C')}
    (β : Id (ap (constant-fibered-system A) q) q')
    (r : Id (tr (λ t → t) (ap-binary hom-system p q) g) g')
    {f : hom-system A B} {f' : hom-system A B'} →
    htpy-section-system' p' f f' →
    htpy-section-system' q' (comp-hom-system g f) (comp-hom-system g' f')
  section-system.type
    ( left-whisker-comp-hom-system' {g = g} refl refl refl refl refl H) X =
    ap (section-system.type g) (section-system.type H X)
  section-system.element
    ( left-whisker-comp-hom-system'
      {A = A} {B = B} {g = g} refl refl refl refl refl {f} {f'} H) {X} x =
    ( tr-ap
      ( section-system.type g)
      ( λ X' → section-system.element g {X'})
      ( section-system.type H X)
      ( section-system.element f x)) ∙
    ( ap (section-system.element g) (section-system.element H x))
  section-system.slice
    ( left-whisker-comp-hom-system'
      {A = A} {B = B} {C = C} {g = g} refl refl refl refl refl H) X =
    left-whisker-comp-hom-system'
      ( ap (system.slice B) (section-system.type H X))
      ( inv
        ( ap-comp
          ( constant-fibered-system (system.slice A X))
          ( system.slice B)
          ( section-system.type H X)))
      ( ap (system.slice C ∘ section-system.type g) (section-system.type H X))
      ( ( ap
          ( ap (constant-fibered-system (system.slice A X)))
          ( ap-comp
            ( system.slice C)
            ( section-system.type g)
            ( section-system.type H X))) ∙
        ( inv
          ( ap-comp
            ( constant-fibered-system (system.slice A X))
            ( system.slice C)
            ( ap (section-system.type g) (section-system.type H X)))))
      ( γ (section-system.type H X))
      ( section-system.slice H X)
      where
      γ : {Y Y' : system.type B} (p : Y ＝ Y') →
          Id
            ( tr
              ( λ t → t)
              ( ap-binary hom-system
                ( ap (system.slice B) p)
                ( ap (system.slice C ∘ section-system.type g) p))
              ( section-system.slice g Y))
            ( section-system.slice g Y')
      γ refl = refl

  left-whisker-comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : system l3 l4}
    {C : system l5 l6} (g : hom-system B C) {f f' : hom-system A B} →
    htpy-hom-system f f' →
    htpy-hom-system (comp-hom-system g f) (comp-hom-system g f')
  left-whisker-comp-hom-system g H =
    left-whisker-comp-hom-system' refl refl refl refl refl H

  right-whisker-comp-hom-system' :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : system l3 l4}
    {C C' : system l5 l6} (p : C ＝ C') {g : hom-system B C}
    {g' : hom-system B C'}
    {p' : Id (constant-fibered-system B C) (constant-fibered-system B C')}
    (α : Id (ap (constant-fibered-system B) p) p')
    {q' : Id (constant-fibered-system A C) (constant-fibered-system A C')}
    (β : Id (ap (constant-fibered-system A) p) q')
    (H : htpy-section-system' p' g g') →
    (f : hom-system A B) →
    htpy-section-system' q' (comp-hom-system g f) (comp-hom-system g' f)
  section-system.type (right-whisker-comp-hom-system' refl refl refl H f) X =
    section-system.type H (section-system.type f X)
  section-system.element
    ( right-whisker-comp-hom-system' refl refl refl H f) x =
    section-system.element H (section-system.element f x)
  section-system.slice
    ( right-whisker-comp-hom-system'
      {A = A} {B = B} {C = C} refl refl refl H f) X =
    right-whisker-comp-hom-system'
      ( ap (system.slice C) (section-system.type H (section-system.type f X)))
      ( inv
        ( ap-comp
          ( constant-fibered-system (system.slice B (section-system.type f X)))
          ( system.slice C)
          ( section-system.type H (section-system.type f X))))
      ( inv
        ( ap-comp
          ( constant-fibered-system (system.slice A X))
          ( system.slice C)
          ( section-system.type H (section-system.type f X))))
      ( section-system.slice H (section-system.type f X))
      ( section-system.slice f X)

  right-whisker-comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : system l3 l4}
    {C : system l5 l6} {g g' : hom-system B C}
    (H : htpy-section-system g g') →
    (f : hom-system A B) →
    htpy-section-system (comp-hom-system g f) (comp-hom-system g' f)
  right-whisker-comp-hom-system H f =
    right-whisker-comp-hom-system' refl refl refl H f
```

---

## Structures on dependent type theories

Dependent type theories are systems equipped with weakening and substitution
structure, and with the structure of generic elements (the variable rule).

### Weakening structure on systems

```agda
  record weakening {l1 l2 : Level} (A : system l1 l2) : UU (lsuc l1 ⊔ lsuc l2)
    where
    coinductive
    field
      type : (X : system.type A) → hom-system A (system.slice A X)
      slice : (X : system.type A) → weakening (system.slice A X)
```

### Morphisms preserving weakening structure

We state what it means for a morphism to preserve weakening structure.

```agda
  record preserves-weakening
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (WA : weakening A) (WB : weakening B) (h : hom-system A B) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        htpy-hom-system
          ( comp-hom-system
            ( section-system.slice h X)
            ( weakening.type WA X))
          ( comp-hom-system
            ( weakening.type WB (section-system.type h X))
            ( h))
      slice :
        (X : system.type A) →
        preserves-weakening
          ( weakening.slice WA X)
          ( weakening.slice WB (section-system.type h X))
          ( section-system.slice h X)
```

### Substitution structure on systems

We introduce substitution structure on a system.

```agda
  record substitution {l1 l2 : Level} (A : system l1 l2) :
    UU (lsuc l1 ⊔ lsuc l2)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        hom-system (system.slice A X) A
      slice : (X : system.type A) → substitution (system.slice A X)
```

### Morphisms preserving substitution structure

We state what it means for a morphism to preserve substitution structure.

```agda
  record preserves-substitution
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    (SA : substitution A) (SB : substitution B) (h : hom-system A B) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        htpy-hom-system
          ( comp-hom-system
            ( h)
            ( substitution.type SA x))
          ( comp-hom-system
            ( substitution.type SB
              ( section-system.element h x))
            ( section-system.slice h X))
      slice :
        (X : system.type A) →
        preserves-substitution
          ( substitution.slice SA X)
          ( substitution.slice SB (section-system.type h X))
          ( section-system.slice h X)
```

### The structure of a generic element on a system equipped with weakening structure

We introduce the structure of a generic element on a system equipped with
weakening structure.

```agda
  record generic-element
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        system.element
          ( system.slice A X)
            ( section-system.type (weakening.type W X) X)
      slice :
        (X : system.type A) → generic-element (weakening.slice W X)

  record preserves-generic-element
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    {WA : weakening A} (δA : generic-element WA)
    {WB : weakening B} (δB : generic-element WB)
    {h : hom-system A B} (Wh : preserves-weakening WA WB h) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        Id ( tr
              ( system.element (system.slice B (section-system.type h X)))
              ( section-system.type
                ( preserves-weakening.type Wh X)
                ( X))
              ( section-system.element
                ( section-system.slice h X)
                ( generic-element.type δA X)))
            ( generic-element.type δB (section-system.type h X))
      slice :
        (X : system.type A) →
        preserves-generic-element
          ( generic-element.slice δA X)
          ( generic-element.slice δB (section-system.type h X))
          ( preserves-weakening.slice Wh X)
```

### Weakening and substitution morphisms preserve weakening, substitution, and generic elements

In a dependent type theory, every weakening morphism and every substitution
morphism preserve both the weakening and substitution structure, and they also
preserve generic elements.

For example, the rule that states that weakening preserves weakening (on types)
can be displayed as follows:

```text
        Γ ⊢ A type          Γ,Δ ⊢ B type          Γ,Δ,Ε ⊢ C type
  ------------------------------------------------------------------------
  Γ,A,W(A,Δ),W(A,B),W(W(A,B),W(A,E)) ⊢ W(W(A,B),W(A,C))=W(A,W(B,C)) type
```

Furthermore, there are laws that state that substitution by `a : A` cancels
weakening by `A`, that substituting a:A in the generic element of `A` gives us
the element a back, and that substituting by the generic element of `A` cancels
weakening by `A`.

We will now state these laws.

```agda
  record weakening-preserves-weakening
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        preserves-weakening W (weakening.slice W X) (weakening.type W X)
      slice :
        (X : system.type A) →
        weakening-preserves-weakening (weakening.slice W X)

  record substitution-preserves-substitution
    {l1 l2 : Level} {A : system l1 l2} (S : substitution A) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        preserves-substitution
          ( substitution.slice S X)
          ( S)
          ( substitution.type S x)
      slice :
        (X : system.type A) →
        substitution-preserves-substitution (substitution.slice S X)

  record weakening-preserves-substitution
    {l1 l2 : Level} {A : system l1 l2} (S : substitution A) (W : weakening A) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        preserves-substitution
          ( S)
          ( substitution.slice S X)
          ( weakening.type W X)
      slice :
        (X : system.type A) →
        weakening-preserves-substitution
          ( substitution.slice S X)
          ( weakening.slice W X)

  record substitution-preserves-weakening
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) (S : substitution A) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        preserves-weakening
          ( weakening.slice W X)
          ( W)
          ( substitution.type S x)
      slice :
        (X : system.type A) →
        substitution-preserves-weakening
          ( weakening.slice W X)
          ( substitution.slice S X)

  record weakening-preserves-generic-element
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A)
    (WW : weakening-preserves-weakening W) (δ : generic-element W) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        preserves-generic-element
          ( δ)
          ( generic-element.slice δ X)
          ( weakening-preserves-weakening.type WW X)
      slice :
        (X : system.type A) →
        weakening-preserves-generic-element
          ( weakening.slice W X)
          ( weakening-preserves-weakening.slice WW X)
          ( generic-element.slice δ X)

  record substitution-preserves-generic-element
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A)
    (δ : generic-element W) (S : substitution A)
    (SW : substitution-preserves-weakening W S) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        preserves-generic-element
          ( generic-element.slice δ X)
          ( δ)
          ( substitution-preserves-weakening.type SW x)
      slice :
        (X : system.type A) →
        substitution-preserves-generic-element
          ( weakening.slice W X)
          ( generic-element.slice δ X)
          ( substitution.slice S X)
          ( substitution-preserves-weakening.slice SW X)

  record substitution-cancels-weakening
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) (S : substitution A) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        htpy-hom-system
          ( comp-hom-system
            ( substitution.type S x)
            ( weakening.type W X))
          ( id-hom-system A)
      slice :
        (X : system.type A) →
        substitution-cancels-weakening
          ( weakening.slice W X)
          ( substitution.slice S X)

  record generic-element-is-identity
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) (S : substitution A)
    (δ : generic-element W) (S!W : substitution-cancels-weakening W S) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        Id
          ( tr
            ( system.element A)
            ( section-system.type
              ( substitution-cancels-weakening.type S!W x) X)
            ( section-system.element
              ( substitution.type S x)
              ( generic-element.type δ X)))
          ( x)
      slice :
        (X : system.type A) →
        generic-element-is-identity
          ( weakening.slice W X)
          ( substitution.slice S X)
          ( generic-element.slice δ X)
          ( substitution-cancels-weakening.slice S!W X)

  record substitution-by-generic-element
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) (S : substitution A)
    (δ : generic-element W) :
    UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        htpy-hom-system
          ( comp-hom-system
            ( substitution.type
              ( substitution.slice S X)
              ( generic-element.type δ X))
            ( weakening.type
              ( weakening.slice W X)
              ( section-system.type (weakening.type W X) X)))
          ( id-hom-system (system.slice A X))
      slice :
        (X : system.type A) →
        substitution-by-generic-element
          ( weakening.slice W X)
          ( substitution.slice S X)
          ( generic-element.slice δ X)
```

### Complete definition of a dependent type theory

We complete the definition of a dependent type theory.

```agda
  record type-theory
    (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
    where
    field
      sys : system l1 l2
      W : weakening sys
      S : substitution sys
      δ : generic-element W
      WW : weakening-preserves-weakening W
      SS : substitution-preserves-substitution S
      WS : weakening-preserves-substitution S W
      SW : substitution-preserves-weakening W S
      Wδ : weakening-preserves-generic-element W WW δ
      Sδ : substitution-preserves-generic-element W δ S SW
      S!W : substitution-cancels-weakening W S
      δid : generic-element-is-identity W S δ S!W
      Sδ! : substitution-by-generic-element W S δ

  closed-type-dtt :
    {l1 l2 : Level} (A : type-theory l1 l2) → UU l1
  closed-type-dtt A = system.type (type-theory.sys A)

  global-element-dtt :
    {l1 l2 : Level} (A : type-theory l1 l2) → closed-type-dtt A → UU l2
  global-element-dtt A = system.element (type-theory.sys A)

  weakening-dtt :
    {l1 l2 : Level} (A : type-theory l1 l2) (X : closed-type-dtt A) →
    hom-system
      ( type-theory.sys A)
      ( system.slice (type-theory.sys A) X)
  weakening-dtt A = weakening.type (type-theory.W A)
```

### The slice of a dependent type theory

We introduce the slice of a dependent type theory.

```agda
  slice-dtt :
    {l1 l2 : Level} (A : type-theory l1 l2)
    (X : system.type (type-theory.sys A)) →
    type-theory l1 l2
  type-theory.sys (slice-dtt A X) =
    system.slice (type-theory.sys A) X
  type-theory.W (slice-dtt A X) =
    weakening.slice (type-theory.W A) X
  type-theory.S (slice-dtt A X) =
    substitution.slice (type-theory.S A) X
  type-theory.δ (slice-dtt A X) =
    generic-element.slice (type-theory.δ A) X
  type-theory.WW (slice-dtt A X) =
    weakening-preserves-weakening.slice (type-theory.WW A) X
  type-theory.SS (slice-dtt A X) =
    substitution-preserves-substitution.slice (type-theory.SS A) X
  type-theory.WS (slice-dtt A X) =
    weakening-preserves-substitution.slice (type-theory.WS A) X
  type-theory.SW (slice-dtt A X) =
    substitution-preserves-weakening.slice (type-theory.SW A) X
  type-theory.Wδ (slice-dtt A X) =
    weakening-preserves-generic-element.slice (type-theory.Wδ A) X
  type-theory.Sδ (slice-dtt A X) =
    substitution-preserves-generic-element.slice (type-theory.Sδ A) X
  type-theory.S!W (slice-dtt A X) =
    substitution-cancels-weakening.slice (type-theory.S!W A) X
  type-theory.δid (slice-dtt A X) =
    generic-element-is-identity.slice (type-theory.δid A) X
  type-theory.Sδ! (slice-dtt A X) =
    substitution-by-generic-element.slice (type-theory.Sδ! A) X
```

### Morphisms of dependent type theories

```agda
  record hom-dtt
    {l1 l2 l3 l4 : Level}
    (A : type-theory l1 l2) (B : type-theory l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    field
      sys :
        hom-system
          ( type-theory.sys A)
          ( type-theory.sys B)
      W :
        preserves-weakening
          ( type-theory.W A)
          ( type-theory.W B)
          ( sys)
      S :
        preserves-substitution
          ( type-theory.S A)
          ( type-theory.S B)
          ( sys)
      δ :
        preserves-generic-element
          ( type-theory.δ A)
          ( type-theory.δ B)
          ( W)

  hom-slice-dtt :
    {l1 l2 l3 l4 : Level} {A : type-theory l1 l2} {B : type-theory l3 l4}
    (f : hom-dtt A B) (X : system.type (type-theory.sys A)) →
    hom-dtt
      ( slice-dtt A X)
      ( slice-dtt B (section-system.type (hom-dtt.sys f) X))
  hom-dtt.sys (hom-slice-dtt f X) =
    section-system.slice (hom-dtt.sys f) X
  hom-dtt.W (hom-slice-dtt f X) =
    preserves-weakening.slice (hom-dtt.W f) X
  hom-dtt.S (hom-slice-dtt f X) =
    preserves-substitution.slice (hom-dtt.S f) X
  hom-dtt.δ (hom-slice-dtt f X) =
    preserves-generic-element.slice (hom-dtt.δ f) X
```

### The identity morphism of a dependent type theory

```agda
  preserves-weakening-id-hom-system :
    {l1 l2 : Level} {A : system l1 l2} (W : weakening A) →
    preserves-weakening W W (id-hom-system A)
  preserves-weakening.type (preserves-weakening-id-hom-system W) X =
    concat-htpy-hom-system
      ( left-unit-law-comp-hom-system (weakening.type W X))
      ( inv-htpy-hom-system
        ( right-unit-law-comp-hom-system (weakening.type W X)))
  preserves-weakening.slice (preserves-weakening-id-hom-system W) X =
    preserves-weakening-id-hom-system (weakening.slice W X)

  preserves-substitution-id-hom-system :
    {l1 l2 : Level} {A : system l1 l2} (S : substitution A) →
    preserves-substitution S S (id-hom-system A)
  preserves-substitution.type (preserves-substitution-id-hom-system S) x =
    concat-htpy-hom-system
      ( left-unit-law-comp-hom-system (substitution.type S x))
      ( inv-htpy-hom-system
        ( right-unit-law-comp-hom-system (substitution.type S x)))
  preserves-substitution.slice (preserves-substitution-id-hom-system S) X =
    preserves-substitution-id-hom-system (substitution.slice S X)

  preserves-generic-element-id-hom-system :
    {l1 l2 : Level} {A : system l1 l2} {W : weakening A}
    (δ : generic-element W) →
    preserves-generic-element δ δ
      ( preserves-weakening-id-hom-system W)
  preserves-generic-element.type
    ( preserves-generic-element-id-hom-system δ) X = refl
  preserves-generic-element.slice
    ( preserves-generic-element-id-hom-system δ) X =
    preserves-generic-element-id-hom-system (generic-element.slice δ X)

  id-hom-dtt :
    {l1 l2 : Level} (A : type-theory l1 l2) → hom-dtt A A
  hom-dtt.sys (id-hom-dtt A) =
    id-hom-system (type-theory.sys A)
  hom-dtt.W (id-hom-dtt A) =
    preserves-weakening-id-hom-system (type-theory.W A)
  hom-dtt.S (id-hom-dtt A) =
    preserves-substitution-id-hom-system (type-theory.S A)
  hom-dtt.δ (id-hom-dtt A) =
    preserves-generic-element-id-hom-system (type-theory.δ A)
```

### The composition of morphisms of type theories

```agda
  preserves-weakening-comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : system l3 l4}
    {C : system l5 l6} {g : hom-system B C} {f : hom-system A B}
    {WA : weakening A} {WB : weakening B} {WC : weakening C} →
    preserves-weakening WB WC g → preserves-weakening WA WB f →
    preserves-weakening WA WC (comp-hom-system g f)
  preserves-weakening.type
    ( preserves-weakening-comp-hom-system {g = g} {f} {WA} {WB} {WC} Wg Wf)
    ( X) =
    concat-htpy-hom-system
      ( associative-comp-hom-system
        ( section-system.slice g (section-system.type f X))
        ( section-system.slice f X)
        ( weakening.type WA X))
      ( concat-htpy-hom-system
        ( left-whisker-comp-hom-system
          ( section-system.slice g (section-system.type f X))
          ( preserves-weakening.type Wf X))
        ( concat-htpy-hom-system
          ( inv-htpy-hom-system
            ( associative-comp-hom-system
              ( section-system.slice g (section-system.type f X))
              ( weakening.type WB (section-system.type f X))
              ( f)))
          ( concat-htpy-hom-system
            ( right-whisker-comp-hom-system
              ( preserves-weakening.type Wg (section-system.type f X))
              ( f))
            ( associative-comp-hom-system
              ( weakening.type WC
                ( section-system.type g (section-system.type f X)))
              ( g)
              ( f)))))
  preserves-weakening.slice
    ( preserves-weakening-comp-hom-system {f = f} Wg Wf) X =
    preserves-weakening-comp-hom-system
      ( preserves-weakening.slice Wg (section-system.type f X))
      ( preserves-weakening.slice Wf X)

  preserves-substitution-comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : system l3 l4}
    {C : system l5 l6} {g : hom-system B C} {f : hom-system A B}
    {SA : substitution A} {SB : substitution B} {SC : substitution C} →
    preserves-substitution SB SC g → preserves-substitution SA SB f →
    preserves-substitution SA SC (comp-hom-system g f)
  preserves-substitution.type
    ( preserves-substitution-comp-hom-system
      {g = g} {f} {SA} {SB} {SC} Sg Sf) {X} x =
    concat-htpy-hom-system
      ( associative-comp-hom-system g f (substitution.type SA x))
      ( concat-htpy-hom-system
        ( left-whisker-comp-hom-system g
          ( preserves-substitution.type Sf x))
        ( concat-htpy-hom-system
          ( inv-htpy-hom-system
            ( associative-comp-hom-system g
              ( substitution.type SB
                ( section-system.element f x))
              ( section-system.slice f X)))
          ( concat-htpy-hom-system
            ( right-whisker-comp-hom-system
              ( preserves-substitution.type Sg
                ( section-system.element f x))
              ( section-system.slice f X))
            ( associative-comp-hom-system
              ( substitution.type SC
                ( section-system.element g (section-system.element f x)))
              ( section-system.slice g (section-system.type f X))
              ( section-system.slice f X)))))
  preserves-substitution.slice
    ( preserves-substitution-comp-hom-system {f = f} Sg Sf) X =
    preserves-substitution-comp-hom-system
      ( preserves-substitution.slice Sg (section-system.type f X))
      ( preserves-substitution.slice Sf X)

  preserves-generic-element-comp-hom-system :
    {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : system l3 l4}
    {C : system l5 l6} {g : hom-system B C} {f : hom-system A B}
    {WA : weakening A} {WB : weakening B} {WC : weakening C} →
    {δA : generic-element WA} {δB : generic-element WB}
    {δC : generic-element WC} →
    {Wg : preserves-weakening WB WC g} {Wf : preserves-weakening WA WB f} →
    (δg : preserves-generic-element δB δC Wg)
    (δf : preserves-generic-element δA δB Wf) →
    preserves-generic-element
      δA δC (preserves-weakening-comp-hom-system Wg Wf)
  preserves-generic-element.type
    ( preserves-generic-element-comp-hom-system
      {A = A} {B} {C} {g} {f} {WA} {WB} {WC} {δA} {δB} {δC} {Wg} {Wf} δg δf) X =
    ( ap
      ( λ t →
        tr
          ( system.element
            ( system.slice C (section-system.type (comp-hom-system g f) X)))
          ( t)
          ( section-system.element
            ( section-system.slice (comp-hom-system g f) X)
            ( generic-element.type δA X)))
      ( left-whisker-concat α right-unit)) ∙
    ( ( tr-concat
        { B =
          system.element
            ( system.slice C (section-system.type (comp-hom-system g f) X))}
        ( α)
        ( β)
        ( section-system.element
          ( section-system.slice (comp-hom-system g f) X)
          ( generic-element.type δA X))) ∙
      ( ( ap
          ( tr
            ( system.element
              ( system.slice C
                ( section-system.type (comp-hom-system g f) X)))
            ( β))
          ( ( γ ( section-system.type (preserves-weakening.type Wf X) X)
                ( section-system.element
                  ( section-system.slice f X)
                  ( generic-element.type δA X))) ∙
            ( ap
              ( section-system.element
                ( section-system.slice g (section-system.type f X)))
              ( preserves-generic-element.type δf X)))) ∙
        ( preserves-generic-element.type δg (section-system.type f X))))
    where
    α =
      ap
        ( section-system.type
          ( section-system.slice g (section-system.type f X)))
        ( section-system.type (preserves-weakening.type Wf X) X)
    β =
      section-system.type
        ( preserves-weakening.type Wg (section-system.type f X))
        ( section-system.type f X)
    γ :
      { Y : system.type (system.slice B (section-system.type f X))}
      ( p :
        Id
          ( Y)
          ( section-system.type
            ( comp-hom-system
              ( weakening.type WB (section-system.type f X))
              ( f))
            ( X)))
      ( u : system.element (system.slice B (section-system.type f X)) Y) →
        Id
          ( tr
            ( system.element
              ( system.slice
                ( C)
                ( section-system.type (comp-hom-system g f) X)))
            ( ap
              ( section-system.type
                ( section-system.slice g (section-system.type f X)))
              ( p))
            ( section-system.element
              ( section-system.slice g (section-system.type f X))
              ( u)))
          ( section-system.element
            ( section-system.slice g (section-system.type f X))
            ( tr
              ( system.element (system.slice B (section-system.type f X)))
              ( p)
              ( u)))
    γ refl u = refl
  preserves-generic-element.slice
    ( preserves-generic-element-comp-hom-system {f = f} δg δf) X =
    preserves-generic-element-comp-hom-system
      ( preserves-generic-element.slice δg (section-system.type f X))
      ( preserves-generic-element.slice δf X)

  comp-hom-dtt :
    {l1 l2 l3 l4 l5 l6 : Level}
    {A : type-theory l1 l2} {B : type-theory l3 l4}
    {C : type-theory l5 l6} →
    hom-dtt B C → hom-dtt A B → hom-dtt A C
  hom-dtt.sys (comp-hom-dtt g f) =
    comp-hom-system (hom-dtt.sys g) (hom-dtt.sys f)
  hom-dtt.W (comp-hom-dtt g f) =
    preserves-weakening-comp-hom-system (hom-dtt.W g) (hom-dtt.W f)
  hom-dtt.S (comp-hom-dtt g f) =
    preserves-substitution-comp-hom-system (hom-dtt.S g) (hom-dtt.S f)
  hom-dtt.δ (comp-hom-dtt g f) =
    preserves-generic-element-comp-hom-system (hom-dtt.δ g) (hom-dtt.δ f)
```

### Homotopies of morphisms of dependent type theories

```agda
  htpy-hom-dtt :
    {l1 l2 l3 l4 : Level}
    {A : type-theory l1 l2} {B : type-theory l3 l4}
    (f g : hom-dtt A B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-dtt f g = htpy-hom-system (hom-dtt.sys f) (hom-dtt.sys g)

  left-unit-law-comp-hom-dtt :
    {l1 l2 l3 l4 : Level}
    {A : type-theory l1 l2} {B : type-theory l3 l4}
    (f : hom-dtt A B) → htpy-hom-dtt (comp-hom-dtt (id-hom-dtt B) f) f
  left-unit-law-comp-hom-dtt f =
    left-unit-law-comp-hom-system (hom-dtt.sys f)

  right-unit-law-comp-hom-dtt :
    {l1 l2 l3 l4 : Level}
    {A : type-theory l1 l2} {B : type-theory l3 l4}
    (f : hom-dtt A B) → htpy-hom-dtt (comp-hom-dtt f (id-hom-dtt A)) f
  right-unit-law-comp-hom-dtt f =
    right-unit-law-comp-hom-system (hom-dtt.sys f)

  associative-comp-hom-dtt :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
    {A : type-theory l1 l2} {B : type-theory l3 l4}
    {C : type-theory l5 l6} {D : type-theory l7 l8}
    (h : hom-dtt C D) (g : hom-dtt B C) (f : hom-dtt A B) →
    htpy-hom-dtt
      ( comp-hom-dtt (comp-hom-dtt h g) f)
      ( comp-hom-dtt h (comp-hom-dtt g f))
  associative-comp-hom-dtt h g f =
    associative-comp-hom-system
      (hom-dtt.sys h) (hom-dtt.sys g) (hom-dtt.sys f)
```

---

### Simple type theories

```agda
  record is-simple-type-theory
    {l1 l2 : Level} (A : type-theory l1 l2) : UU l1
    where
    coinductive
    field
      type :
        (X : system.type (type-theory.sys A)) →
        is-equiv
          ( section-system.type
            ( weakening.type (type-theory.W A) X))
      slice :
        (X : system.type (type-theory.sys A)) →
        is-simple-type-theory (slice-dtt A X)

  record simple-type-theory (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
    where
    field
      dtt : type-theory l1 l2
      is-simple : is-simple-type-theory dtt
```

### The condition that the action on elements of a morphism of dependent type theories is an equivalence

We introduce the condition that the action on elements of a morphism of
dependent type theories is an equivalence.

```agda
  record is-equiv-on-elements-hom-system
    {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4)
    (h : hom-system A B) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        (X : system.type A) → is-equiv (section-system.element h {X})
      slice :
        (X : system.type A) →
        is-equiv-on-elements-hom-system
          ( system.slice A X)
          ( system.slice B (section-system.type h X))
          ( section-system.slice h X)
```

### Unary type theories

```agda
  record unary-type-theory
    {l1 l2 : Level} (A : type-theory l1 l2) : UU (lsuc l1 ⊔ lsuc l2)
    where
    field
      dtt : type-theory l1 l2
      is-simple : is-simple-type-theory A
      is-unary :
        (X Y : system.type (type-theory.sys A)) →
        is-equiv-on-elements-hom-system
          ( system.slice (type-theory.sys A) Y)
          ( system.slice
            ( system.slice (type-theory.sys A) X)
            ( section-system.type
              ( weakening.type (type-theory.W A) X) Y))
          ( section-system.slice
            ( weakening.type (type-theory.W A) X)
            ( Y))
```

### Proof irrelevant type theories

```agda
  record is-proof-irrelevant-type-theory
    {l1 l2 : Level} (A : type-theory l1 l2) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      type :
        (X : system.type (type-theory.sys A)) →
        is-prop (system.element (type-theory.sys A) X)
      slice :
        (X : system.type (type-theory.sys A)) →
        is-proof-irrelevant-type-theory (slice-dtt A X)
```

---

```agda
  system-Slice : {l : Level} (X : UU l) → system (lsuc l) l
  system.type (system-Slice {l} X) = X → UU l
  system.element (system-Slice X) Y = (x : X) → Y x
  system.slice (system-Slice X) Y = system-Slice (Σ X Y)

  {-
  hom-system-weakening-system-Slice :
    {l : Level} (X : UU l) (Y : X → UU l) →
    hom-system (system-Slice X) (system-Slice (Σ X Y))
  section-system.type (hom-system-weakening-system-Slice X Y) Z (pair x y) =
    Z x
  section-system.element
    (hom-system-weakening-system-Slice X Y) Z g (pair x y) =
    g x
  section-system.type
    (section-system.slice (hom-system-weakening-system-Slice X Y) Z)
    W (pair (pair x y) z) =
    W (pair x z)
  section-system.element
    (section-system.slice (hom-system-weakening-system-Slice X Y) Z)
    W h (pair (pair x y) z) =
    h (pair x z)
  section-system.slice
    (section-system.slice (hom-system-weakening-system-Slice X Y) Z) W =
    {!section-system.slice (hom-system-weakening-system-Slice X Y) ?!}

  weakening-system-Slice :
    {l : Level} (X : UU l) → weakening (system-Slice X)
  weakening.type (weakening-system-Slice X) Y =
    hom-system-weakening-system-Slice X Y
  weakening.slice (weakening-system-Slice X) = {!!}

  system-UU : (l : Level) → system (lsuc l) l
  system.type (system-UU l) = UU l
  system.element (system-UU l) X = X
  system.slice (system-UU l) X = system-Slice X

  weakening-type-UU :
    {l : Level} (X : UU l) →
    hom-system (system-UU l) (system.slice (system-UU l) X)
  section-system.type (weakening-type-UU X) Y x = Y
  section-system.element (weakening-type-UU X) Y y x = y
  section-system.slice (weakening-type-UU X) Y = {!!}

  weakening-UU : (l : Level) → weakening (system-UU l)
  section-system.type (weakening.type (weakening-UU l) X) Y x = Y
  section-system.element (weakening.type (weakening-UU l) X) Y y x = y
  section-system.type
    (section-system.slice (weakening.type (weakening-UU l) X) Y) Z t =
    Z (pr2 t)
  section-system.element
    ( section-system.slice (weakening.type (weakening-UU l) X) Y) Z f t =
    f (pr2 t)
  section-system.slice
    (section-system.slice (weakening.type (weakening-UU l) X) Y) Z =
    {!!}
  section-system.type
    ( weakening.type (weakening.slice (weakening-UU l) X) Y) Z (pair x y) =
    Z x
  section-system.element
    ( weakening.type (weakening.slice (weakening-UU l) X) Y) Z f (pair x y) =
    f x
  section-system.slice
    (weakening.type (weakening.slice (weakening-UU l) X) Y) Z =
    {!!}
  weakening.slice (weakening.slice (weakening-UU l) X) Y =
    weakening.slice (weakening-UU l) (Σ X Y)
-}
```

---

### Dependent type theories with Π-types

We define what it means for a dependent type theory to have Π-types.

```agda
  record function-types
    {l1 l2 : Level} (A : type-theory l1 l2) : UU (l1 ⊔ l2)
    where
    coinductive
    field
      sys :
        (X : system.type (type-theory.sys A)) →
        hom-dtt (slice-dtt A X) A
      app :
        (X : system.type (type-theory.sys A)) →
        is-equiv-on-elements-hom-system
          ( type-theory.sys (slice-dtt A X))
          ( type-theory.sys A)
          ( hom-dtt.sys (sys X))
      slice :
        (X : system.type (type-theory.sys A)) →
        function-types (slice-dtt A X)

  {-
  record preserves-function-types
    {l1 l2 l3 l4 : Level} {A : type-theory l1 l2}
    {B : type-theory l3 l4} (ΠA : function-types A)
    (ΠB : function-types B) (h : hom-dtt A B) : UU {!!}
    where
    coinductive
    field
      sys   : {!!}
      slice : {!!}
  -}
```

---

```agda
  record natural-numbers
    {l1 l2 : Level} (A : type-theory l1 l2) (Π : function-types A) :
    UU (l1 ⊔ l2)
    where
    field
      N : closed-type-dtt A
      zero : global-element-dtt A N
      succ :
        global-element-dtt A
          ( section-system.type
            ( hom-dtt.sys (function-types.sys Π N))
            ( section-system.type
              ( weakening.type (type-theory.W A) N)
              ( N)))

  {-
  natural-numbers-slice :
    {l1 l2 : Level} (A : type-theory l1 l2) (Π : function-types A)
    (N : natural-numbers A Π) (X : closed-type-dtt A) →
    natural-numbers (slice-dtt A X) (function-types.slice Π X)
  natural-numbers.N (natural-numbers-slice A Π N X) =
    section-system.type
      ( weakening.type (type-theory.W A) X)
      ( natural-numbers.N N)
  natural-numbers.zero (natural-numbers-slice A Π N X) =
    section-system.element
      ( weakening.type (type-theory.W A) X)
      ( natural-numbers.N N)
      ( natural-numbers.zero N)
  natural-numbers.succ (natural-numbers-slice A Π N X) =
    tr ( system.element (type-theory.sys (slice-dtt A X)))
       {! (section-system.type
          (preserves-weakening.type
          (hom-dtt.W (function-types.sys Π (natural-numbers.N N))) ?) ?)!}
    {-
    Id ( section-system.type
         ( weakening.type (type-theory.W A) X)
         ( section-system.type
           ( hom-dtt.sys (function-types.sys Π (natural-numbers.N N)))
           ( section-system.type
             ( weakening.type (type-theory.W A) (natural-numbers.N N))
             (natural-numbers.N N))))
       ( section-system.type
         ( hom-dtt.sys
           ( function-types.sys (function-types.slice Π X)
             ( natural-numbers.N (natural-numbers-slice A Π N X))))
         ( section-system.type
           ( weakening.type
             ( type-theory.W (slice-dtt A X))
             ( natural-numbers.N (natural-numbers-slice A Π N X)))
           ( natural-numbers.N (natural-numbers-slice A Π N X))))
  -}
       ( section-system.element
         ( weakening.type (type-theory.W A) X)
         ( section-system.type
           ( hom-dtt.sys (function-types.sys Π (natural-numbers.N N)))
           ( section-system.type
             ( weakening.type (type-theory.W A) (natural-numbers.N N))
             ( natural-numbers.N N)))
         ( natural-numbers.succ N))
  -}
```

---

```agda
  {-
  concat-htpy-hom-system' :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B B' B'' : system l3 l4}
    (p : B ＝ B') (q : B' ＝ B'') {f : hom-system A B} {g : hom-system A B'}
    {h : hom-system A B''} → htpy-hom-system' p f g → htpy-hom-system' q g h →
    htpy-hom-system' (p ∙ q) f h
  htpy-hom-system'.type (concat-htpy-hom-system' refl refl H K) =
    htpy-hom-system'.type H ∙h htpy-hom-system'.type K
  htpy-hom-system'.element
    ( concat-htpy-hom-system' {A = A} {B} {.B} refl refl {f} H K) X x =
    ( ( tr-concat
        ( section-system.type H X)
        ( section-system.type K X)
        ( section-system.element (tr (hom-system A) refl f) X x)) ∙
      ( ap
        ( tr (system.element B) (section-system.type K X))
        ( section-system.element H X x))) ∙
    ( section-system.element K X x)
  htpy-hom-system'.slice (concat-htpy-hom-system' p q H K) = {!!}

  concat-htpy-hom-system :
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
    {f g h : hom-system A B} (H : htpy-hom-system f g)
    (K : htpy-hom-system g h) → htpy-hom-system f h
  htpy-hom-system'.type (concat-htpy-hom-system H K) =
    section-system.type H ∙h section-system.type K
  htpy-hom-system'.element
    ( concat-htpy-hom-system {A = A} {B = B} {f} H K) X x =
    ( ( tr-concat
        ( section-system.type H X)
        ( section-system.type K X)
        ( section-system.element (tr (hom-system A) refl f) X x)) ∙
      ( ap
        ( tr (system.element B) (section-system.type K X))
        ( section-system.element H X x))) ∙
    ( section-system.element K X x)
  htpy-hom-system'.slice (concat-htpy-hom-system H K) X = {!!}
  -}
```

---

## Contexts in a dependent type theory

We interpret contexts in a dependent type theory.

```agda
module c-system where

  open dependent

  data context
    {l1 l2 : Level} (A : type-theory l1 l2) : UU l1
    where
    empty-ctx : context A
    extension-ctx :
      (X : system.type (type-theory.sys A))
      (Γ : context (slice-dtt A X)) → context A
```

### The action on contexts of a morphism of dependent type theories

```agda
  context-hom :
    {l1 l2 l3 l4 : Level} {A : type-theory l1 l2}
    {B : type-theory l3 l4} (f : hom-dtt A B) →
    context A → context B
  context-hom f empty-ctx = empty-ctx
  context-hom f (extension-ctx X Γ) =
    extension-ctx
      ( section-system.type (hom-dtt.sys f) X)
      ( context-hom (hom-slice-dtt f X) Γ)
```

### Elements of contexts

```agda
{-
  data element-context
    {l1 l2 : Level} {A : type-theory l1 l2} :
    (Γ : context A) → UU {!substitution.type (type-theory.S A) !}
    where
    element-empty-context : element-context empty-ctx
    element-extension-ctx :
      {!(X : system.type (type-theory.sys A))
        (Γ : context (slice-dtt A X))
        (x : system.element (type-theory.sys A) X)
        (y : element-context
              (context-hom (substitution.type (type-theory.S A) x) Γ)) →
        element-context (extension-ctx X Γ)!}
-}
```

### Interpreting types in context in a dependent type theory

```agda
  type :
    {l1 l2 : Level} (A : type-theory l1 l2) →
    context A → UU l1
  type A empty-ctx = system.type (type-theory.sys A)
  type A (extension-ctx X Γ) = type (slice-dtt A X) Γ
```

### Interpreting elements of types in context in a dependent type theory

```agda
  element :
    {l1 l2 : Level} (A : type-theory l1 l2) (Γ : context A)
    (Y : type A Γ) → UU l2
  element A empty-ctx = system.element (type-theory.sys A)
  element A (extension-ctx X Γ) = element (slice-dtt A X) Γ

  slice :
    {l1 l2 : Level} (A : type-theory l1 l2) (Γ : context A) →
    type-theory l1 l2
  slice A empty-ctx = A
  slice A (extension-ctx X Γ) = slice (slice-dtt A X) Γ

  dependent-context :
    {l1 l2 : Level} (A : type-theory l1 l2) (Γ : context A) →
    UU l1
  dependent-context A Γ = context (slice A Γ)

{-
  weakening-by-type-context :
    {l1 l2 : Level} {A : type-theory l1 l2}
    (X : system.type (type-theory.sys A)) →
    context A → context (slice-dtt A X)
  weakening-by-type-context {A = A} X Δ =
    context-hom {!weakening.type (type-theory.W A) X!} Δ
-}

  weakening-type-context :
    {l1 l2 : Level} (A : type-theory l1 l2) (Γ : context A) →
    system.type (type-theory.sys A) →
    system.type (type-theory.sys (slice A Γ))
  weakening-type-context A empty-ctx Y = Y
  weakening-type-context A (extension-ctx X Γ) Y =
    weakening-type-context (slice-dtt A X) Γ
      ( section-system.type
        ( weakening.type (type-theory.W A) X) Y)

{-
  weakening-context :
    {l1 l2 : Level} (A : type-theory l1 l2) (Γ : context A) →
    context A → context (slice A Γ)
  weakening-context A empty-ctx Δ = Δ
  weakening-context A (extension-ctx X Γ) empty-ctx = empty-ctx
  weakening-context A (extension-ctx X Γ) (extension-ctx Y Δ) =
    extension-ctx
      ( weakening-type-context A (extension-ctx X Γ) Y)
      ( weakening-context {!!} {!!} {!!})
-}
```
