# Cones over cospan diagrams

```agda
open import foundation.function-extensionality-axiom

module foundation.cones-over-cospan-diagrams
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences funext
open import foundation.function-extensionality funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies funext
open import foundation.homotopy-induction funext
open import foundation.identity-types funext
open import foundation.multivariable-homotopies funext
open import foundation.structure-identity-principle
open import foundation.telescopes
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps funext
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
open import foundation-core.whiskering-identifications-concatenation
```

</details>

## Idea

A {{#concept "cone" Disambiguation="cospan diagram" Agda=cone}} over a
[cospan diagram](foundation.cospans.md) `A -f-> X <-g- B` with domain `C` is a
triple `(p, q, H)` consisting of a map `p : C → A`, a map `q : C → B`, and a
[homotopy](foundation-core.homotopies.md) `H` witnessing that the square

```text
        q
    C -----> B
    |        |
  p |        | g
    ∨        ∨
    A -----> X
        f
```

[commutes](foundation-core.commuting-squares-of-maps.md).

## Definitions

### Cones over cospans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where

  cone : {l4 : Level} → UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cone C = Σ (C → A) (λ p → Σ (C → B) (λ q → coherence-square-maps q p g f))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  vertical-map-cone : C → A
  vertical-map-cone = pr1 c

  horizontal-map-cone : C → B
  horizontal-map-cone = pr1 (pr2 c)

  coherence-square-cone :
    coherence-square-maps horizontal-map-cone vertical-map-cone g f
  coherence-square-cone = pr2 (pr2 c)
```

### Dependent cones over cospan diagrams

```agda
cone-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  cone f g C → (C → UU l8) → UU (l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8)
cone-family {C = C} PX {f = f} {g} f' g' c PC =
  (x : C) →
  cone
    ( ( tr PX (coherence-square-cone f g c x)) ∘
      ( f' (vertical-map-cone f g c x)))
    ( g' (horizontal-map-cone f g c x))
    ( PC x)
```

### Characterizing identifications of cones over cospan diagrams

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4}
  where

  coherence-htpy-cone :
    (c c' : cone f g C)
    (K : vertical-map-cone f g c ~ vertical-map-cone f g c')
    (L : horizontal-map-cone f g c ~ horizontal-map-cone f g c') → UU (l4 ⊔ l3)
  coherence-htpy-cone c c' K L =
    ( coherence-square-cone f g c ∙h (g ·l L)) ~
    ( (f ·l K) ∙h coherence-square-cone f g c')

  htpy-cone : cone f g C → cone f g C → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-cone c c' =
    Σ ( vertical-map-cone f g c ~ vertical-map-cone f g c')
      ( λ K →
        Σ ( horizontal-map-cone f g c ~ horizontal-map-cone f g c')
          ( coherence-htpy-cone c c' K))

  htpy-vertical-map-htpy-cone :
    (c c' : cone f g C) (H : htpy-cone c c') →
    vertical-map-cone f g c ~ vertical-map-cone f g c'
  htpy-vertical-map-htpy-cone c c' H = pr1 H

  htpy-horizontal-map-htpy-cone :
    (c c' : cone f g C) (H : htpy-cone c c') →
    horizontal-map-cone f g c ~ horizontal-map-cone f g c'
  htpy-horizontal-map-htpy-cone c c' H = pr1 (pr2 H)

  coh-htpy-cone :
    (c c' : cone f g C) (H : htpy-cone c c') →
    coherence-htpy-cone c c'
      ( htpy-vertical-map-htpy-cone c c' H)
      ( htpy-horizontal-map-htpy-cone c c' H)
  coh-htpy-cone c c' H = pr2 (pr2 H)

  refl-htpy-cone : (c : cone f g C) → htpy-cone c c
  pr1 (refl-htpy-cone c) = refl-htpy
  pr1 (pr2 (refl-htpy-cone c)) = refl-htpy
  pr2 (pr2 (refl-htpy-cone c)) = right-unit-htpy

  htpy-eq-cone : (c c' : cone f g C) → c ＝ c' → htpy-cone c c'
  htpy-eq-cone c .c refl = refl-htpy-cone c

  is-torsorial-htpy-cone :
    (c : cone f g C) → is-torsorial (htpy-cone c)
  is-torsorial-htpy-cone c =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (vertical-map-cone f g c))
      ( vertical-map-cone f g c , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy (horizontal-map-cone f g c))
        ( horizontal-map-cone f g c , refl-htpy)
        ( is-torsorial-htpy (coherence-square-cone f g c ∙h refl-htpy)))

  is-equiv-htpy-eq-cone : (c c' : cone f g C) → is-equiv (htpy-eq-cone c c')
  is-equiv-htpy-eq-cone c =
    fundamental-theorem-id (is-torsorial-htpy-cone c) (htpy-eq-cone c)

  extensionality-cone : (c c' : cone f g C) → (c ＝ c') ≃ htpy-cone c c'
  pr1 (extensionality-cone c c') = htpy-eq-cone c c'
  pr2 (extensionality-cone c c') = is-equiv-htpy-eq-cone c c'

  eq-htpy-cone : (c c' : cone f g C) → htpy-cone c c' → c ＝ c'
  eq-htpy-cone c c' = map-inv-equiv (extensionality-cone c c')
```

### Precomposing cones over cospan diagrams with a map

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where

  cone-map :
    {C : UU l4} → cone f g C → {C' : UU l5} → (C' → C) → cone f g C'
  pr1 (cone-map c h) = vertical-map-cone f g c ∘ h
  pr1 (pr2 (cone-map c h)) = horizontal-map-cone f g c ∘ h
  pr2 (pr2 (cone-map c h)) = coherence-square-cone f g c ·r h
```

### Pasting cones horizontally

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where

  pasting-horizontal-cone :
    (c : cone j h B) → cone i (vertical-map-cone j h c) A → cone (j ∘ i) h A
  pr1 (pasting-horizontal-cone c (f , p , H)) = f
  pr1 (pr2 (pasting-horizontal-cone c (f , p , H))) =
    (horizontal-map-cone j h c) ∘ p
  pr2 (pr2 (pasting-horizontal-cone c (f , p , H))) =
    pasting-horizontal-coherence-square-maps p
      ( horizontal-map-cone j h c)
      ( f)
      ( vertical-map-cone j h c)
      ( h)
      ( i)
      ( j)
      ( H)
      ( coherence-square-cone j h c)
```

### Vertical composition of cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  where

  pasting-vertical-cone :
    (c : cone f g B) → cone (horizontal-map-cone f g c) h A → cone f (g ∘ h) A
  pr1 (pasting-vertical-cone c (p' , q' , H')) =
    ( vertical-map-cone f g c) ∘ p'
  pr1 (pr2 (pasting-vertical-cone c (p' , q' , H'))) = q'
  pr2 (pr2 (pasting-vertical-cone c (p' , q' , H'))) =
    pasting-vertical-coherence-square-maps q' p' h
      ( horizontal-map-cone f g c)
      ( vertical-map-cone f g c)
      ( g)
      ( f)
      ( H')
      ( coherence-square-cone f g c)
```

### The swapping function on cones over cospans

```agda
swap-cone :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) → cone f g C → cone g f C
pr1 (swap-cone f g c) = horizontal-map-cone f g c
pr1 (pr2 (swap-cone f g c)) = vertical-map-cone f g c
pr2 (pr2 (swap-cone f g c)) = inv-htpy (coherence-square-cone f g c)
```

### Parallel cones over parallel cospan diagrams

Two cones with the same domain over parallel cospans are considered
{{#concept "parallel" Disambiguation="cones over parallel cospan diagrams"}} if
they are part of a fully coherent diagram: there is a fully coherent cube where
all the vertical maps are identities, the top face is given by one cone, and the
bottom face is given by the other.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  coherence-htpy-parallel-cone :
    {l4 : Level} {C : UU l4} (c : cone f g C) (c' : cone f' g' C)
    (Hp : vertical-map-cone f g c ~ vertical-map-cone f' g' c')
    (Hq : horizontal-map-cone f g c ~ horizontal-map-cone f' g' c') →
    UU (l3 ⊔ l4)
  coherence-htpy-parallel-cone c c' Hp Hq =
    ( ( coherence-square-cone f g c) ∙h
      ( (g ·l Hq) ∙h (Hg ·r horizontal-map-cone f' g' c'))) ~
    ( ( (f ·l Hp) ∙h (Hf ·r (vertical-map-cone f' g' c'))) ∙h
      ( coherence-square-cone f' g' c'))

  fam-htpy-parallel-cone :
    {l4 : Level} {C : UU l4} (c : cone f g C) → (c' : cone f' g' C) →
    (vertical-map-cone f g c ~ vertical-map-cone f' g' c') → UU (l2 ⊔ l3 ⊔ l4)
  fam-htpy-parallel-cone c c' Hp =
    Σ ( horizontal-map-cone f g c ~ horizontal-map-cone f' g' c')
      ( coherence-htpy-parallel-cone c c' Hp)

  htpy-parallel-cone :
    {l4 : Level} {C : UU l4} →
    cone f g C → cone f' g' C → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-parallel-cone c c' =
    Σ ( vertical-map-cone f g c ~ vertical-map-cone f' g' c')
      ( fam-htpy-parallel-cone c c')
```

### The identity cone over the identity cospan

```agda
id-cone : {l : Level} (A : UU l) → cone (id {A = A}) (id {A = A}) A
id-cone A = (id , id , refl-htpy)
```

## Properties

### Relating `htpy-parallel-cone` to the identity type of cones

In the following part we relate the type `htpy-parallel-cone` to the identity
type of cones. We show that `htpy-parallel-cone` characterizes
[dependent identifications](foundation.dependent-identifications.md) of cones on
the same domain over parallel cospans.

**Note.** The characterization relies heavily on
[function extensionality](foundation.function-extensionality.md).

#### The type family of homotopies of parallel cones is torsorial

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f : A → X} {g : B → X}
  where

  refl-htpy-parallel-cone :
    (c : cone f g C) →
    htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c
  pr1 (refl-htpy-parallel-cone c) = refl-htpy
  pr1 (pr2 (refl-htpy-parallel-cone c)) = refl-htpy
  pr2 (pr2 (refl-htpy-parallel-cone c)) = right-unit-htpy

  htpy-eq-degenerate-parallel-cone :
    (c c' : cone f g C) →
    c ＝ c' →
    htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c'
  htpy-eq-degenerate-parallel-cone c .c refl = refl-htpy-parallel-cone c

  htpy-parallel-cone-refl-htpy-htpy-cone :
    (c c' : cone f g C) →
    htpy-cone f g c c' →
    htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c'
  htpy-parallel-cone-refl-htpy-htpy-cone (p , q , H) (p' , q' , H') =
    tot
      ( λ K →
        tot
          ( λ L M →
            ( ap-concat-htpy H right-unit-htpy) ∙h
            ( M ∙h ap-concat-htpy' H' inv-htpy-right-unit-htpy)))

  abstract
    is-equiv-htpy-parallel-cone-refl-htpy-htpy-cone :
      (c c' : cone f g C) →
      is-equiv (htpy-parallel-cone-refl-htpy-htpy-cone c c')
    is-equiv-htpy-parallel-cone-refl-htpy-htpy-cone (p , q , H) (p' , q' , H') =
      is-equiv-tot-is-fiberwise-equiv
        ( λ K →
          is-equiv-tot-is-fiberwise-equiv
            ( λ L →
              is-equiv-comp
                ( concat-htpy
                  ( ap-concat-htpy H right-unit-htpy)
                  ( (f ·l K) ∙h refl-htpy ∙h H'))
                ( concat-htpy'
                  ( H ∙h (g ·l L))
                  ( ap-concat-htpy' H' inv-htpy-right-unit-htpy))
                ( is-equiv-concat-htpy'
                  ( H ∙h (g ·l L))
                  ( λ x → right-whisker-concat (inv right-unit) (H' x)))
                ( is-equiv-concat-htpy
                  ( λ x → left-whisker-concat (H x) right-unit)
                  ( (f ·l K) ∙h refl-htpy ∙h H'))))

  abstract
    is-torsorial-htpy-parallel-cone-refl-htpy-refl-htpy :
      (c : cone f g C) →
      is-torsorial (htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c)
    is-torsorial-htpy-parallel-cone-refl-htpy-refl-htpy c =
      is-contr-is-equiv'
        ( Σ (cone f g C) (htpy-cone f g c))
        ( tot (htpy-parallel-cone-refl-htpy-htpy-cone c))
        ( is-equiv-tot-is-fiberwise-equiv
          ( is-equiv-htpy-parallel-cone-refl-htpy-htpy-cone c))
        ( is-torsorial-htpy-cone f g c)

  abstract
    is-torsorial-htpy-parallel-cone-refl-htpy :
      {g' : B → X} (Hg : g ~ g') (c : cone f g C) →
      is-torsorial (htpy-parallel-cone (refl-htpy' f) Hg c)
    is-torsorial-htpy-parallel-cone-refl-htpy =
      ind-htpy
        ( g)
        ( λ g'' Hg' →
          (c : cone f g C) →
          is-torsorial (htpy-parallel-cone (refl-htpy' f) Hg' c))
        ( is-torsorial-htpy-parallel-cone-refl-htpy-refl-htpy)

  abstract
    is-torsorial-htpy-parallel-cone :
      {f' : A → X} (Hf : f ~ f') {g' : B → X} (Hg : g ~ g') (c : cone f g C) →
      is-torsorial (htpy-parallel-cone Hf Hg c)
    is-torsorial-htpy-parallel-cone Hf {g'} =
      ind-htpy
        ( f)
        ( λ f'' Hf' →
          (g' : B → X) (Hg : g ~ g') (c : cone f g C) →
          is-contr (Σ (cone f'' g' C) (htpy-parallel-cone Hf' Hg c)))
        ( λ g' Hg → is-torsorial-htpy-parallel-cone-refl-htpy Hg)
        ( Hf)
        ( g')
```

#### The type family of homotopies of parallel cones characterizes dependent identifications of cones on the same domain over parallel cospans

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f : A → X} {g : B → X}
  where

  tr-right-tr-left-cone-eq-htpy :
    {f' : A → X} → f ~ f' → {g' : B → X} → g ~ g' → cone f g C → cone f' g' C
  tr-right-tr-left-cone-eq-htpy {f'} Hf Hg c =
    tr
      ( λ y → cone f' y C)
      ( eq-htpy Hg)
      ( tr (λ x → cone x g C) (eq-htpy Hf) c)

  compute-tr-right-tr-left-cone-eq-htpy-refl-htpy :
    (c : cone f g C) →
    tr-right-tr-left-cone-eq-htpy refl-htpy refl-htpy c ＝ c
  compute-tr-right-tr-left-cone-eq-htpy-refl-htpy c =
    ( ap
      ( λ t →
        tr
          ( λ g'' → cone f g'' C)
          ( t)
          ( tr (λ x → cone x g C) (eq-htpy (refl-htpy' f)) c))
      ( eq-htpy-refl-htpy g)) ∙
    ( ap (λ t → tr (λ f''' → cone f''' g C) t c) (eq-htpy-refl-htpy f))

  htpy-eq-parallel-cone-refl-htpy :
    (c c' : cone f g C) →
    tr-right-tr-left-cone-eq-htpy refl-htpy refl-htpy c ＝ c' →
    htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c'
  htpy-eq-parallel-cone-refl-htpy c c' =
    map-inv-is-equiv-precomp-Π-is-equiv
      ( is-equiv-concat (compute-tr-right-tr-left-cone-eq-htpy-refl-htpy c) c')
      ( λ p → htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c')
      ( htpy-eq-degenerate-parallel-cone c c')

  left-map-triangle-eq-parallel-cone-refl-htpy :
    (c c' : cone f g C) →
    ( ( htpy-eq-parallel-cone-refl-htpy c c') ∘
      ( concat (compute-tr-right-tr-left-cone-eq-htpy-refl-htpy c) c')) ~
    ( htpy-eq-degenerate-parallel-cone c c')
  left-map-triangle-eq-parallel-cone-refl-htpy c c' =
    is-section-map-inv-is-equiv-precomp-Π-is-equiv
      ( is-equiv-concat (compute-tr-right-tr-left-cone-eq-htpy-refl-htpy c) c')
      ( λ p → htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c')
      ( htpy-eq-degenerate-parallel-cone c c')

  abstract
    htpy-parallel-cone-dependent-eq' :
      {g' : B → X} (Hg : g ~ g') →
      (c : cone f g C) (c' : cone f g' C) →
      tr-right-tr-left-cone-eq-htpy refl-htpy Hg c ＝ c' →
      htpy-parallel-cone (refl-htpy' f) Hg c c'
    htpy-parallel-cone-dependent-eq' =
      ind-htpy g
        ( λ g'' Hg' →
          ( c : cone f g C) (c' : cone f g'' C) →
          tr-right-tr-left-cone-eq-htpy refl-htpy Hg' c ＝ c' →
          htpy-parallel-cone refl-htpy Hg' c c')
        ( htpy-eq-parallel-cone-refl-htpy)

    left-map-triangle-parallel-cone-eq' :
      (c c' : cone f g C) →
      ( ( htpy-parallel-cone-dependent-eq' refl-htpy c c') ∘
        ( concat (compute-tr-right-tr-left-cone-eq-htpy-refl-htpy c) c')) ~
      ( htpy-eq-degenerate-parallel-cone c c')
    left-map-triangle-parallel-cone-eq' c c' =
      ( right-whisker-comp
        ( multivariable-htpy-eq 3
          ( compute-ind-htpy g
            ( λ g'' Hg' →
              ( c : cone f g C) (c' : cone f g'' C) →
              tr-right-tr-left-cone-eq-htpy refl-htpy Hg' c ＝ c' →
              htpy-parallel-cone refl-htpy Hg' c c')
            ( htpy-eq-parallel-cone-refl-htpy))
          ( c)
          ( c'))
        ( concat (compute-tr-right-tr-left-cone-eq-htpy-refl-htpy c) c')) ∙h
      ( left-map-triangle-eq-parallel-cone-refl-htpy c c')

  abstract
    htpy-parallel-cone-dependent-eq :
      {f' : A → X} (Hf : f ~ f') {g' : B → X} (Hg : g ~ g') →
      (c : cone f g C) (c' : cone f' g' C) →
      tr-right-tr-left-cone-eq-htpy Hf Hg c ＝ c' →
      htpy-parallel-cone Hf Hg c c'
    htpy-parallel-cone-dependent-eq {f'} Hf {g'} Hg c c' p =
      ind-htpy f
        ( λ f'' Hf' →
          ( g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f'' g' C) →
          ( tr-right-tr-left-cone-eq-htpy Hf' Hg c ＝ c') →
          htpy-parallel-cone Hf' Hg c c')
        ( λ g' → htpy-parallel-cone-dependent-eq' {g' = g'})
        Hf g' Hg c c' p

    left-map-triangle-parallel-cone-eq :
      (c c' : cone f g C) →
      ( ( htpy-parallel-cone-dependent-eq refl-htpy refl-htpy c c') ∘
        ( concat (compute-tr-right-tr-left-cone-eq-htpy-refl-htpy c) c')) ~
      ( htpy-eq-degenerate-parallel-cone c c')
    left-map-triangle-parallel-cone-eq c c' =
      ( right-whisker-comp
        ( multivariable-htpy-eq 5
          ( compute-ind-htpy f
            ( λ f'' Hf' →
              ( g' : B → X) (Hg : g ~ g')
              (c : cone f g C) (c' : cone f'' g' C) →
              ( tr-right-tr-left-cone-eq-htpy Hf' Hg c ＝ c') →
              htpy-parallel-cone Hf' Hg c c')
            ( λ g' → htpy-parallel-cone-dependent-eq' {g' = g'}))
          ( g)
          ( refl-htpy)
          ( c)
          ( c'))
        ( concat (compute-tr-right-tr-left-cone-eq-htpy-refl-htpy c) c')) ∙h
      ( left-map-triangle-parallel-cone-eq' c c')

  abstract
    is-fiberwise-equiv-htpy-parallel-cone-dependent-eq :
      {f' : A → X} (Hf : f ~ f') {g' : B → X} (Hg : g ~ g') →
      (c : cone f g C) (c' : cone f' g' C) →
      is-equiv (htpy-parallel-cone-dependent-eq Hf Hg c c')
    is-fiberwise-equiv-htpy-parallel-cone-dependent-eq {f'} Hf {g'} Hg c c' =
      ind-htpy f
        ( λ f' Hf →
          ( g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f' g' C) →
            is-equiv (htpy-parallel-cone-dependent-eq Hf Hg c c'))
        ( λ g' Hg c c' →
          ind-htpy g
            ( λ g' Hg →
              ( c : cone f g C) (c' : cone f g' C) →
                is-equiv (htpy-parallel-cone-dependent-eq refl-htpy Hg c c'))
            ( λ c c' →
              is-equiv-right-map-triangle
                ( htpy-eq-degenerate-parallel-cone c c')
                ( htpy-parallel-cone-dependent-eq refl-htpy refl-htpy c c')
                ( concat (compute-tr-right-tr-left-cone-eq-htpy-refl-htpy c) c')
                ( inv-htpy (left-map-triangle-parallel-cone-eq c c'))
                ( fundamental-theorem-id
                  ( is-torsorial-htpy-parallel-cone
                    ( refl-htpy' f)
                    ( refl-htpy' g)
                    ( c))
                  ( htpy-eq-degenerate-parallel-cone c) c')
                ( is-equiv-concat
                  ( compute-tr-right-tr-left-cone-eq-htpy-refl-htpy c)
                  ( c')))
            ( Hg)
            ( c)
            ( c'))
        ( Hf)
        ( g')
        ( Hg)
        ( c)
        ( c')

  dependent-eq-htpy-parallel-cone :
    {f' : A → X} (Hf : f ~ f') {g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f' g' C) →
    htpy-parallel-cone Hf Hg c c' →
    tr-right-tr-left-cone-eq-htpy Hf Hg c ＝ c'
  dependent-eq-htpy-parallel-cone Hf Hg c c' =
    map-inv-is-equiv
      ( is-fiberwise-equiv-htpy-parallel-cone-dependent-eq Hf Hg c c')
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
