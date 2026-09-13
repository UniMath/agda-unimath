# Dependent cocones under spans

```agda
module synthetic-homotopy-theory.dependent-cocones-under-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.constant-type-families
open import foundation.contractible-types
open import foundation.dependent-homotopies
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-contractible-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-higher-identifications
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.injective-maps

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

dependent-cocone-span-diagram :
  { l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3} {X : UU l4}
  ( c : cocone-span-diagram 𝒮 X) (P : X → UU l5) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
dependent-cocone-span-diagram {𝒮 = 𝒮} =
  dependent-cocone (left-map-span-diagram 𝒮) (right-map-span-diagram 𝒮)
```

### Cocones equipped with dependent cocones

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (P : X → UU l5)
  where

  cocone-with-dependent-cocone : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  cocone-with-dependent-cocone =
    Σ (cocone f g X) (λ c → dependent-cocone f g c P)

module _
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (P : X → UU l5)
  (c : cocone-with-dependent-cocone f g P)
  where

  cocone-cocone-with-dependent-cocone : cocone f g X
  cocone-cocone-with-dependent-cocone = pr1 c

  horizontal-map-cocone-with-dependent-cocone : A → X
  horizontal-map-cocone-with-dependent-cocone =
    horizontal-map-cocone f g cocone-cocone-with-dependent-cocone

  vertical-map-cocone-with-dependent-cocone : B → X
  vertical-map-cocone-with-dependent-cocone =
    vertical-map-cocone f g cocone-cocone-with-dependent-cocone

  coherence-square-cocone-with-dependent-cocone :
    coherence-square-maps g f
      ( vertical-map-cocone-with-dependent-cocone)
      ( horizontal-map-cocone-with-dependent-cocone)
  coherence-square-cocone-with-dependent-cocone =
    coherence-square-cocone f g cocone-cocone-with-dependent-cocone

  dependent-cocone-cocone-with-dependent-cocone :
    dependent-cocone f g cocone-cocone-with-dependent-cocone P
  dependent-cocone-cocone-with-dependent-cocone = pr2 c

  horizontal-map-dependent-cocone-with-dependent-cocone :
    (a : A) → P (horizontal-map-cocone-with-dependent-cocone a)
  horizontal-map-dependent-cocone-with-dependent-cocone =
    horizontal-map-dependent-cocone f g
      ( cocone-cocone-with-dependent-cocone)
      ( P)
      ( dependent-cocone-cocone-with-dependent-cocone)

  vertical-map-dependent-cocone-with-dependent-cocone :
    (b : B) → P (vertical-map-cocone-with-dependent-cocone b)
  vertical-map-dependent-cocone-with-dependent-cocone =
    vertical-map-dependent-cocone f g
      ( cocone-cocone-with-dependent-cocone)
      ( P)
      ( dependent-cocone-cocone-with-dependent-cocone)

  coherence-square-dependent-cocone-with-dependent-cocone :
    (s : S) →
    dependent-identification P
      ( coherence-square-cocone-with-dependent-cocone s)
      ( horizontal-map-dependent-cocone-with-dependent-cocone (f s))
      ( vertical-map-dependent-cocone-with-dependent-cocone (g s))
  coherence-square-dependent-cocone-with-dependent-cocone =
    coherence-square-dependent-cocone f g
      ( cocone-cocone-with-dependent-cocone)
      ( P)
      ( dependent-cocone-cocone-with-dependent-cocone)
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

dependent-cocone-map-span-diagram :
  { l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3} {X : UU l4}
  ( c : cocone-span-diagram 𝒮 X) (P : X → UU l5) →
  ( (x : X) → P x) → dependent-cocone-span-diagram c P
dependent-cocone-map-span-diagram {𝒮 = 𝒮} c =
  dependent-cocone-map (left-map-span-diagram 𝒮) (right-map-span-diagram 𝒮) c
```

## Properties

### Characterization of identifications of dependent cocones over a fixed cocone

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

### Dependent homotopies of dependent cocones over homotopies of cocones

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} (f : S → A) (g : S → B)
  {X : UU l4}
  where

  coherence-dependent-htpy-dependent-cocone :
    ( c c' : cocone f g X) (H : htpy-cocone f g c c') (P : X → UU l5)
    ( d : dependent-cocone f g c P)
    ( d' : dependent-cocone f g c' P) →
    dependent-homotopy (λ _ → P)
      ( horizontal-htpy-cocone f g c c' H)
      ( horizontal-map-dependent-cocone f g c P d)
      ( horizontal-map-dependent-cocone f g c' P d') →
    dependent-homotopy (λ _ → P)
      ( vertical-htpy-cocone f g c c' H)
      ( vertical-map-dependent-cocone f g c P d)
      ( vertical-map-dependent-cocone f g c' P d') →
    UU (l1 ⊔ l5)
  coherence-dependent-htpy-dependent-cocone c c' H P d d' K L =
    (s : S) →
    dependent-identification² P
      ( coherence-htpy-cocone f g c c' H s)
      ( concat-dependent-identification P
        ( coherence-square-cocone f g c s)
        ( vertical-htpy-cocone f g c c' H (g s))
        ( coherence-square-dependent-cocone f g c P d s)
        ( L (g s)))
      ( concat-dependent-identification P
        ( horizontal-htpy-cocone f g c c' H (f s))
        ( coherence-square-cocone f g c' s)
        ( K (f s))
        ( coherence-square-dependent-cocone f g c' P d' s))

  dependent-htpy-dependent-cocone :
    ( c c' : cocone f g X) (H : htpy-cocone f g c c') (P : X → UU l5)
    ( d : dependent-cocone f g c P) (d' : dependent-cocone f g c' P) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
  dependent-htpy-dependent-cocone c c' H P d d' =
    Σ ( dependent-homotopy (λ _ → P)
        ( horizontal-htpy-cocone f g c c' H)
        ( horizontal-map-dependent-cocone f g c P d)
        ( horizontal-map-dependent-cocone f g c' P d'))
      ( λ K →
        Σ ( dependent-homotopy (λ _ → P)
            ( vertical-htpy-cocone f g c c' H)
            ( vertical-map-dependent-cocone f g c P d)
            ( vertical-map-dependent-cocone f g c' P d'))
          ( coherence-dependent-htpy-dependent-cocone c c' H P d d' K))

  refl-dependent-htpy-dependent-cocone :
    ( c : cocone f g X) (P : X → UU l5) (d : dependent-cocone f g c P) →
    dependent-htpy-dependent-cocone c c (refl-htpy-cocone f g c) P d d
  pr1 (refl-dependent-htpy-dependent-cocone c P d) = refl-htpy
  pr1 (pr2 (refl-dependent-htpy-dependent-cocone c P d)) = refl-htpy
  pr2 (pr2 (refl-dependent-htpy-dependent-cocone c P d)) s =
    right-unit-dependent-identification P
      ( coherence-square-cocone f g c s)
      ( coherence-square-dependent-cocone f g c P d s)

  dependent-htpy-dependent-eq-dependent-cocone :
    (c c' : cocone f g X) (p : c ＝ c') (P : X → UU l5)
    (d : dependent-cocone f g c P) (d' : dependent-cocone f g c' P) →
    dependent-identification (λ c'' → dependent-cocone f g c'' P) p d d' →
    dependent-htpy-dependent-cocone c c' (htpy-eq-cocone f g c c' p) P d d'
  dependent-htpy-dependent-eq-dependent-cocone c .c refl P d ._ refl =
    refl-dependent-htpy-dependent-cocone c P d

  abstract
    is-torsorial-dependent-htpy-over-refl-dependent-cocone :
      (c : cocone f g X) (P : X → UU l5) (d : dependent-cocone f g c P) →
      is-torsorial
        ( dependent-htpy-dependent-cocone c c (refl-htpy-cocone f g c) P d)
    is-torsorial-dependent-htpy-over-refl-dependent-cocone c P d =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy _)
        ( horizontal-map-dependent-cocone f g c P d , refl-htpy)
        ( is-torsorial-Eq-structure
          ( is-torsorial-htpy _)
          ( vertical-map-dependent-cocone f g c P d , refl-htpy)
          ( is-torsorial-htpy _))
```

#### Characterizing equality of cocones equipped with dependent cocones

We now move to characterize equality of cocones equipped with dependent cocones,
from which it follows that dependent homotopies of dependent cocones
characterize dependent identifications of them.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} (f : S → A) (g : S → B)
  {X : UU l4} (P : X → UU l5)
  where

  htpy-cocone-with-dependent-cocone :
    (c c' : cocone-with-dependent-cocone f g P) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  htpy-cocone-with-dependent-cocone c c' =
    Σ ( htpy-cocone f g
        ( cocone-cocone-with-dependent-cocone f g P c)
        ( cocone-cocone-with-dependent-cocone f g P c'))
      ( λ H →
        dependent-htpy-dependent-cocone f g
          ( cocone-cocone-with-dependent-cocone f g P c)
          ( cocone-cocone-with-dependent-cocone f g P c')
          ( H)
          ( P)
          ( dependent-cocone-cocone-with-dependent-cocone f g P c)
          ( dependent-cocone-cocone-with-dependent-cocone f g P c'))

  refl-htpy-cocone-with-dependent-cocone :
    (c : cocone-with-dependent-cocone f g P) →
    htpy-cocone-with-dependent-cocone c c
  pr1 (refl-htpy-cocone-with-dependent-cocone c) =
    refl-htpy-cocone f g (cocone-cocone-with-dependent-cocone f g P c)
  pr2 (refl-htpy-cocone-with-dependent-cocone c) =
    refl-dependent-htpy-dependent-cocone f g
      ( cocone-cocone-with-dependent-cocone f g P c)
      ( P)
      ( dependent-cocone-cocone-with-dependent-cocone f g P c)

  htpy-eq-cocone-with-dependent-cocone :
    (c c' : cocone-with-dependent-cocone f g P) →
    c ＝ c' →
    htpy-cocone-with-dependent-cocone c c'
  htpy-eq-cocone-with-dependent-cocone c .c refl =
    refl-htpy-cocone-with-dependent-cocone c

  abstract
    is-torsorial-htpy-cocone-with-dependent-cocone :
      (c : cocone-with-dependent-cocone f g P) →
      is-torsorial (htpy-cocone-with-dependent-cocone c)
    is-torsorial-htpy-cocone-with-dependent-cocone c =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy-cocone f g
          ( cocone-cocone-with-dependent-cocone f g P c))
        ( cocone-cocone-with-dependent-cocone f g P c ,
          refl-htpy-cocone f g (cocone-cocone-with-dependent-cocone f g P c))
        ( is-torsorial-dependent-htpy-over-refl-dependent-cocone f g
          ( cocone-cocone-with-dependent-cocone f g P c)
          ( P)
          ( dependent-cocone-cocone-with-dependent-cocone f g P c))

  abstract
    is-equiv-htpy-eq-cocone-with-dependent-cocone :
      (c c' : cocone-with-dependent-cocone f g P) →
      is-equiv (htpy-eq-cocone-with-dependent-cocone c c')
    is-equiv-htpy-eq-cocone-with-dependent-cocone c =
      fundamental-theorem-id
        ( is-torsorial-htpy-cocone-with-dependent-cocone c)
        ( htpy-eq-cocone-with-dependent-cocone c)

  eq-htpy-cocone-with-dependent-cocone :
    (c c' : cocone-with-dependent-cocone f g P) →
    htpy-cocone-with-dependent-cocone c c' → c ＝ c'
  eq-htpy-cocone-with-dependent-cocone c c' =
    map-inv-is-equiv (is-equiv-htpy-eq-cocone-with-dependent-cocone c c')

  extensionality-cocone-with-dependent-cocone :
    (c c' : cocone-with-dependent-cocone f g P) →
    (c ＝ c') ≃ htpy-cocone-with-dependent-cocone c c'
  extensionality-cocone-with-dependent-cocone c c' =
    ( htpy-eq-cocone-with-dependent-cocone c c' ,
      is-equiv-htpy-eq-cocone-with-dependent-cocone c c')
```

### Dependent cocones on constant type families are equivalent to nondependent cocones

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
      ( dependent-cocone-constant-type-family-cocone)
      ( cocone-dependent-cocone-constant-type-family)
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
      ( dependent-cocone-constant-type-family-cocone)
      ( cocone-dependent-cocone-constant-type-family)
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

### Computing with the characterization of identifications of dependent cocones on constant type families over a fixed cocone

If two dependent cocones on a constant type family are homotopic, then so are
their nondependent counterparts.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} (f : S → A) (g : S → B)
  {X : UU l4} (c : cocone f g X)
  (Y : UU l5)
  where

  coherence-htpy-cocone-dependent-cocone-coherence-htpy-dependent-cocone-constant-type-family :
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
  coherence-htpy-cocone-dependent-cocone-coherence-htpy-dependent-cocone-constant-type-family
    d d' K L H x =
    ( left-whisker-concat-coherence-square-identifications
      ( inv
        ( tr-constant-type-family
          ( coherence-square-cocone f g c x)
          ( horizontal-map-dependent-cocone f g c (λ _ → Y) d (f x))))
      ( ap (tr (λ _ → Y) (coherence-square-cocone f g c x)) (K (f x)))
      ( coherence-square-dependent-cocone f g c (λ _ → Y) d x)
      ( coherence-square-dependent-cocone f g c (λ _ → Y) d' x)
      ( L (g x))
      ( H x)) ∙
    ( ap
      ( _∙ coherence-square-dependent-cocone f g c (λ _ → Y) d' x)
      ( naturality-inv-tr-constant-type-family
        ( coherence-square-cocone f g c x)
        ( K (f x)))) ∙
    ( assoc
      ( K (f x))
      ( inv
        ( tr-constant-type-family
          ( coherence-square-cocone f g c x)
          ( horizontal-map-dependent-cocone f g c (λ _ → Y) d' (f x))))
      ( coherence-square-dependent-cocone f g c (λ _ → Y) d' x))
```

If the dependent cocones on constant type families constructed from nondependent
cocones are homotopic, then so are the nondependent cocones.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} (f : S → A) (g : S → B)
  {X : UU l4} {Y : UU l5}
  where

  coherence-htpy-cocone-coherence-htpy-dependent-cocone-constant-type-family :
    (c : cocone f g X)
    (d d' : cocone f g Y) →
    ( K : horizontal-map-cocone f g d ~ horizontal-map-cocone f g d')
    ( L : vertical-map-cocone f g d ~ vertical-map-cocone f g d') →
    coherence-htpy-dependent-cocone f g c (λ _ → Y)
      ( dependent-cocone-constant-type-family-cocone f g c d)
      ( dependent-cocone-constant-type-family-cocone f g c d')
      ( K)
      ( L) →
    statement-coherence-htpy-cocone f g
      ( d)
      ( d')
      ( K)
      ( L)
  coherence-htpy-cocone-coherence-htpy-dependent-cocone-constant-type-family
    c d d' K L H x =
    is-injective-concat
      ( tr-constant-type-family
        ( coherence-square-cocone f g c x)
        ( horizontal-map-cocone f g d (f x)))
      ( ( inv
          ( assoc
            ( tr-constant-type-family
              ( coherence-square-cocone f g c x)
              ( horizontal-map-cocone f g d (f x)))
            ( coherence-square-cocone f g d x)
            ( L (g x)))) ∙
        ( H x) ∙
        ( right-whisker-concat-coherence-square-identifications
          ( tr-constant-type-family
            ( coherence-square-cocone f g c x)
            ( horizontal-map-cocone f g d (f x)))
          ( ap (tr (λ _ → Y) (coherence-square-cocone f g c x)) (K (f x)))
          ( K (f x))
          ( tr-constant-type-family
            ( coherence-square-cocone f g c x)
            ( horizontal-map-cocone f g d' (f x)))
          ( inv
            ( naturality-tr-constant-type-family
              ( coherence-square-cocone f g c x)
              ( K (f x))))
          ( coherence-square-cocone f g d' x)))
```
