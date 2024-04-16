# Dependent cocones under spans

```agda
module synthetic-homotopy-theory.dependent-cocones-under-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.constant-type-families
open import foundation.contractible-types
open import foundation.dependent-homotopies
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

Consider a span `𝒮 := (A <-- S --> B)` and a
[cocone structure](synthetic-homotopy-theory.cocones-under-spans.md) `c` of `𝒮`
into a type `X`. Furthermore, consider a type family `P` over `X`. In this case
we may consider _dependent_ cocone structures on `P` over `c`.

A **dependent cocone** `d` over `(i , j , H)` on `P` consists of two dependent
functions

```text
  i' : (a : A) → P (i a)
  j' : (b : B) → P (j b)
```

and a family of
[dependent identifications](foundation.dependent-identifications.md)

```text
  (s : S) → dependent-identification P (H s) (i' (f s)) (j' (g s)).
```

## Definitions

### Dependent cocones

```agda
module _
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X) (P : X → UU l5)
  where

  dependent-cocone : UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
  dependent-cocone =
    Σ ( (a : A) → P (horizontal-map-cocone f g c a))
      ( λ hA →
        Σ ( (b : B) → P (vertical-map-cocone f g c b))
          ( λ hB →
            (s : S) →
            dependent-identification P
              ( coherence-square-cocone f g c s)
              ( hA (f s))
              ( hB (g s))))

  module _
    (d : dependent-cocone)
    where

    horizontal-map-dependent-cocone :
      (a : A) → P (horizontal-map-cocone f g c a)
    horizontal-map-dependent-cocone = pr1 d

    vertical-map-dependent-cocone :
      (b : B) → P (vertical-map-cocone f g c b)
    vertical-map-dependent-cocone = pr1 (pr2 d)

    coherence-square-dependent-cocone :
      (s : S) →
      dependent-identification P
        ( coherence-square-cocone f g c s)
        ( horizontal-map-dependent-cocone (f s))
        ( vertical-map-dependent-cocone (g s))
    coherence-square-dependent-cocone = pr2 (pr2 d)
```

### Postcomposing dependent cocones with maps

```agda
dependent-cocone-map :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X) (P : X → UU l5) →
  ( (x : X) → P x) → dependent-cocone f g c P
pr1 (dependent-cocone-map f g c P h) a =
  h (horizontal-map-cocone f g c a)
pr1 (pr2 (dependent-cocone-map f g c P h)) b =
  h (vertical-map-cocone f g c b)
pr2 (pr2 (dependent-cocone-map f g c P h)) s =
  apd h (coherence-square-cocone f g c s)
```

## Properties

### Characterization of identifications of dependent cocones

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} (f : S → A) (g : S → B)
  {X : UU l4} (c : cocone f g X)
  (P : X → UU l5) (d : dependent-cocone f g c P)
  where

  coherence-htpy-dependent-cocone :
    ( d' : dependent-cocone f g c P) →
    ( horizontal-map-dependent-cocone f g c P d ~
      horizontal-map-dependent-cocone f g c P d') →
    ( vertical-map-dependent-cocone f g c P d ~
      vertical-map-dependent-cocone f g c P d') →
    UU (l1 ⊔ l5)
  coherence-htpy-dependent-cocone d' K L =
    (s : S) →
    ( ( coherence-square-dependent-cocone f g c P d s) ∙ (L (g s))) ＝
    ( ( ap (tr P (coherence-square-cocone f g c s)) (K (f s))) ∙
      ( coherence-square-dependent-cocone f g c P d' s))

  htpy-dependent-cocone :
    (d' : dependent-cocone f g c P) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
  htpy-dependent-cocone d' =
    Σ ( horizontal-map-dependent-cocone f g c P d ~
        horizontal-map-dependent-cocone f g c P d')
      ( λ K →
        Σ ( vertical-map-dependent-cocone f g c P d ~
            vertical-map-dependent-cocone f g c P d')
          ( coherence-htpy-dependent-cocone d' K))

  refl-htpy-dependent-cocone :
    htpy-dependent-cocone d
  pr1 refl-htpy-dependent-cocone = refl-htpy
  pr1 (pr2 refl-htpy-dependent-cocone) = refl-htpy
  pr2 (pr2 refl-htpy-dependent-cocone) = right-unit-htpy

  htpy-eq-dependent-cocone :
    (d' : dependent-cocone f g c P) → d ＝ d' → htpy-dependent-cocone d'
  htpy-eq-dependent-cocone .d refl = refl-htpy-dependent-cocone

  module _
    (d' : dependent-cocone f g c P)
    (p : d ＝ d')
    where

    horizontal-htpy-eq-dependent-cocone :
      horizontal-map-dependent-cocone f g c P d ~
      horizontal-map-dependent-cocone f g c P d'
    horizontal-htpy-eq-dependent-cocone =
      pr1 (htpy-eq-dependent-cocone d' p)

    vertical-htpy-eq-dependent-cocone :
      vertical-map-dependent-cocone f g c P d ~
      vertical-map-dependent-cocone f g c P d'
    vertical-htpy-eq-dependent-cocone =
      pr1 (pr2 (htpy-eq-dependent-cocone d' p))

    coherence-square-htpy-eq-dependent-cocone :
      coherence-htpy-dependent-cocone d'
        ( horizontal-htpy-eq-dependent-cocone)
        ( vertical-htpy-eq-dependent-cocone)
    coherence-square-htpy-eq-dependent-cocone =
      pr2 (pr2 (htpy-eq-dependent-cocone d' p))

  abstract
    is-torsorial-htpy-dependent-cocone :
      is-torsorial htpy-dependent-cocone
    is-torsorial-htpy-dependent-cocone =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (horizontal-map-dependent-cocone f g c P d))
        ( horizontal-map-dependent-cocone f g c P d , refl-htpy)
        ( is-torsorial-Eq-structure
          ( is-torsorial-htpy (vertical-map-dependent-cocone f g c P d))
          ( vertical-map-dependent-cocone f g c P d , refl-htpy)
          ( is-contr-equiv
            ( Σ ( (s : S) →
                  dependent-identification P
                    ( coherence-square-cocone f g c s)
                    ( horizontal-map-dependent-cocone f g c P d (f s))
                    ( vertical-map-dependent-cocone f g c P d (g s)))
                ( λ γ → coherence-square-dependent-cocone f g c P d ~ γ))
            ( equiv-tot (equiv-concat-htpy inv-htpy-right-unit-htpy))
            ( is-torsorial-htpy
              ( coherence-square-dependent-cocone f g c P d))))

  abstract
    is-equiv-htpy-eq-dependent-cocone :
      (d' : dependent-cocone f g c P) → is-equiv (htpy-eq-dependent-cocone d')
    is-equiv-htpy-eq-dependent-cocone =
      fundamental-theorem-id
        ( is-torsorial-htpy-dependent-cocone)
        ( htpy-eq-dependent-cocone)

    eq-htpy-dependent-cocone :
      (d' : dependent-cocone f g c P) → htpy-dependent-cocone d' → d ＝ d'
    eq-htpy-dependent-cocone d' =
      map-inv-is-equiv (is-equiv-htpy-eq-dependent-cocone d')

    is-section-eq-htpy-dependent-cocone :
      (d' : dependent-cocone f g c P) →
      ( htpy-eq-dependent-cocone d' ∘ eq-htpy-dependent-cocone d') ~ id
    is-section-eq-htpy-dependent-cocone d' =
      is-section-map-inv-is-equiv (is-equiv-htpy-eq-dependent-cocone d')

    is-retraction-eq-htpy-dependent-cocone :
      (d' : dependent-cocone f g c P) →
      ( eq-htpy-dependent-cocone d' ∘ htpy-eq-dependent-cocone d') ~ id
    is-retraction-eq-htpy-dependent-cocone d' =
      is-retraction-map-inv-is-equiv (is-equiv-htpy-eq-dependent-cocone d')
```

### Dependent cocones on constant type families

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) {Y : UU l5}
  where

  dependent-cocone-constant-type-family-cocone :
    cocone f g Y → dependent-cocone f g c (λ _ → Y)
  pr1 (dependent-cocone-constant-type-family-cocone (f' , g' , H)) = f'
  pr1 (pr2 (dependent-cocone-constant-type-family-cocone (f' , g' , H))) = g'
  pr2 (pr2 (dependent-cocone-constant-type-family-cocone (f' , g' , H))) s =
    tr-constant-type-family (coherence-square-cocone f g c s) (f' (f s)) ∙ H s

  cocone-dependent-cocone-constant-type-family :
    dependent-cocone f g c (λ _ → Y) → cocone f g Y
  pr1 (cocone-dependent-cocone-constant-type-family (f' , g' , H)) = f'
  pr1 (pr2 (cocone-dependent-cocone-constant-type-family (f' , g' , H))) = g'
  pr2 (pr2 (cocone-dependent-cocone-constant-type-family (f' , g' , H))) s =
    ( inv
      ( tr-constant-type-family (coherence-square-cocone f g c s) (f' (f s)))) ∙
    ( H s)

  is-section-cocone-dependent-cocone-constant-type-family :
    is-section
      dependent-cocone-constant-type-family-cocone
      cocone-dependent-cocone-constant-type-family
  is-section-cocone-dependent-cocone-constant-type-family (f' , g' , H) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( eq-htpy
          ( λ s →
            is-section-inv-concat
              ( tr-constant-type-family
                ( coherence-square-cocone f g c s)
                ( f' (f s)))
              ( H s))))

  is-retraction-cocone-dependent-cocone-constant-type-family :
    is-retraction
      dependent-cocone-constant-type-family-cocone
      cocone-dependent-cocone-constant-type-family
  is-retraction-cocone-dependent-cocone-constant-type-family (f' , g' , H) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( eq-htpy
          ( λ s →
            is-retraction-inv-concat
              ( tr-constant-type-family
                ( coherence-square-cocone f g c s)
                ( f' (f s)))
              ( H s))))

  is-equiv-dependent-cocone-constant-type-family-cocone :
    is-equiv dependent-cocone-constant-type-family-cocone
  is-equiv-dependent-cocone-constant-type-family-cocone =
    is-equiv-is-invertible
      ( cocone-dependent-cocone-constant-type-family)
      ( is-section-cocone-dependent-cocone-constant-type-family)
      ( is-retraction-cocone-dependent-cocone-constant-type-family)

  compute-dependent-cocone-constant-type-family :
    cocone f g Y ≃ dependent-cocone f g c (λ _ → Y)
  compute-dependent-cocone-constant-type-family =
    ( dependent-cocone-constant-type-family-cocone ,
      is-equiv-dependent-cocone-constant-type-family-cocone)
```

### Computing the dependent cocone map on a constant type family

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) {Y : UU l5}
  where

  triangle-dependent-cocone-map-constant-type-family :
    dependent-cocone-map f g c (λ _ → Y) ~
    dependent-cocone-constant-type-family-cocone f g c ∘ cocone-map f g c
  triangle-dependent-cocone-map-constant-type-family h =
    eq-htpy-dependent-cocone f g c
      ( λ _ → Y)
      ( dependent-cocone-map f g c (λ _ → Y) h)
      ( dependent-cocone-constant-type-family-cocone f g c (cocone-map f g c h))
      ( ( refl-htpy) ,
        ( refl-htpy) ,
        ( λ s →
          right-unit ∙
          apd-constant-type-family h (coherence-square-cocone f g c s)))

  triangle-dependent-cocone-map-constant-type-family' :
    cocone-map f g c ~
    cocone-dependent-cocone-constant-type-family f g c ∘
    dependent-cocone-map f g c (λ _ → Y)
  triangle-dependent-cocone-map-constant-type-family' h =
    eq-htpy-cocone f g
      ( cocone-map f g c h)
      ( ( cocone-dependent-cocone-constant-type-family f g c
          ( dependent-cocone-map f g c (λ _ → Y) h)))
      ( ( refl-htpy) ,
        ( refl-htpy) ,
        ( λ s →
          right-unit ∙
          left-transpose-eq-concat
            ( tr-constant-type-family
              ( coherence-square-cocone f g c s)
              ( pr1 (dependent-cocone-map f g c (λ _ → Y) h) (f s)))
            ( ap h (coherence-square-cocone f g c s))
            ( apd h (coherence-square-cocone f g c s))
            ( inv
              ( apd-constant-type-family h (coherence-square-cocone f g c s)))))
```

### The nondependent cocone map at `Y` is an equivalence if and only if the dependent cocone map at the constant type family `(λ _ → Y)` is

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) {Y : UU l5}
  where

  is-equiv-cocone-map-is-equiv-dependent-cocone-map-constant-type-family :
    is-equiv (dependent-cocone-map f g c (λ _ → Y)) →
    is-equiv (cocone-map f g c)
  is-equiv-cocone-map-is-equiv-dependent-cocone-map-constant-type-family =
    is-equiv-top-map-triangle
      ( dependent-cocone-map f g c (λ _ → Y))
      ( dependent-cocone-constant-type-family-cocone f g c)
      ( cocone-map f g c)
      ( triangle-dependent-cocone-map-constant-type-family f g c)
      ( is-equiv-dependent-cocone-constant-type-family-cocone f g c)

  is-equiv-dependent-cocone-map-constant-type-family-is-equiv-cocone-map :
    is-equiv (cocone-map f g c) →
    is-equiv (dependent-cocone-map f g c (λ _ → Y))
  is-equiv-dependent-cocone-map-constant-type-family-is-equiv-cocone-map H =
    is-equiv-left-map-triangle
      ( dependent-cocone-map f g c (λ _ → Y))
      ( dependent-cocone-constant-type-family-cocone f g c)
      ( cocone-map f g c)
      ( triangle-dependent-cocone-map-constant-type-family f g c)
      ( H)
      ( is-equiv-dependent-cocone-constant-type-family-cocone f g c)
```

### Computing with the characterization of identifications of dependent cocones on constant type families

If two dependent cocones on a constant type family are homotopic, then so are
their nondependent counterparts.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} (f : S → A) (g : S → B)
  {X : UU l4} (c : cocone f g X)
  (Y : UU l5)
  where

  coherence-htpy-cocone-coherence-htpy-dependent-cocone-constant-type-family :
    ( d d' : dependent-cocone f g c (λ _ → Y)) →
    ( K :
      horizontal-map-dependent-cocone f g c (λ _ → Y) d ~
      horizontal-map-dependent-cocone f g c (λ _ → Y) d')
    ( L :
      vertical-map-dependent-cocone f g c (λ _ → Y) d ~
      vertical-map-dependent-cocone f g c (λ _ → Y) d')
    ( H : coherence-htpy-dependent-cocone f g c (λ _ → Y) d d' K L) →
    statement-coherence-htpy-cocone f g
      ( cocone-dependent-cocone-constant-type-family f g c d)
      ( cocone-dependent-cocone-constant-type-family f g c d')
      ( K)
      ( L)
  coherence-htpy-cocone-coherence-htpy-dependent-cocone-constant-type-family
    d d' K L H x =
    ( assoc
      ( inv
        ( tr-constant-type-family
          ( coherence-square-cocone f g c x)
          ( horizontal-map-dependent-cocone f g c (λ _ → Y) d (f x))))
      ( coherence-square-dependent-cocone f g c (λ _ → Y) d x)
      ( L (g x))) ∙
    ( ap
      ( inv
        ( tr-constant-type-family
          ( coherence-square-cocone f g c x)
          ( horizontal-map-dependent-cocone f g c (λ _ → Y) d (f x))) ∙_)
      ( H x)) ∙
    ( inv
      ( assoc
        ( inv
          ( tr-constant-type-family
            ( coherence-square-cocone f g c x)
            ( horizontal-map-dependent-cocone f g c (λ _ → Y) d (f x))))
        ( ap (tr (λ _ → Y) (coherence-square-cocone f g c x)) (K (f x)))
        ( coherence-square-dependent-cocone f g c (λ _ → Y) d' x))) ∙
    ap
      ( _∙ coherence-square-dependent-cocone f g c (λ _ → Y) d' x)
      ( naturality-inv-tr-constant-type-family
        ( coherence-square-cocone f g c x)
        ( K (f x))) ∙
    ( assoc
      ( K (f x))
      ( inv
        ( tr-constant-type-family
          ( coherence-square-cocone f g c x)
          ( horizontal-map-dependent-cocone f g c (λ _ → Y) d' (f x))))
      ( coherence-square-dependent-cocone f g c (λ _ → Y) d' x))
```
