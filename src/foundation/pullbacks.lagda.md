# Pullbacks

```agda
module foundation.pullbacks where

open import foundation-core.pullbacks public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.cones-over-cospan-diagrams
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.descent-equivalences
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.multivariable-homotopies
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-extensionality
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.postcomposition-functions
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

Given a [cospan of types](foundation.cospans.md)

```text
  f : A → X ← B : g,
```

we can form the
{{#concept "standard pullback" Disambiguation="types" Agda=standard-pullback}}
`A ×_X B` satisfying
[the universal property of the pullback](foundation-core.universal-property-pullbacks.md)
of the cospan, completing the diagram

```text
  A ×_X B ------> B
     | ⌟          |
     |            | g
     |            |
     v            v
     A ---------> X.
           f
```

The standard pullback consists of [pairs](foundation.dependent-pair-types.md)
`a : A` and `b : B` such that `f a ＝ g b` agree

```text
  A ×_X B := Σ (a : A) (b : B), (f a ＝ g b),
```

thus the standard [cone](foundation.cones-over-cospan-diagrams.md) consists of
the canonical projections.

## Properties

### Being a pullback is a property

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  is-prop-is-pullback : (c : cone f g C) → is-prop (is-pullback f g c)
  is-prop-is-pullback c = is-property-is-equiv (gap f g c)

  is-pullback-Prop : (c : cone f g C) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 (is-pullback-Prop c) = is-pullback f g c
  pr2 (is-pullback-Prop c) = is-prop-is-pullback c
```

### Pullbacks are closed under exponentiation

Given a pullback square

```text
          f'
    C ---------> B
    | ⌟          |
  g'|            | g
    |            |
    v            v
    A ---------> X
          f
```

then the exponentiated square given by postcomposition

```text
                f' ∘ -
      (S → C) ---------> (S → B)
         |                  |
  g' ∘ - |                  | g ∘ -
         |                  |
         v                  v
      (S → A) ---------> (S → X)
                f ∘ -
```

is a pullback square for any type `S`.

```agda
postcomp-cone :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} (T : UU l5)
  (f : A → X) (g : B → X) (c : cone f g C) →
  cone (postcomp T f) (postcomp T g) (T → C)
pr1 (postcomp-cone T f g c) h = vertical-map-cone f g c ∘ h
pr1 (pr2 (postcomp-cone T f g c)) h = horizontal-map-cone f g c ∘ h
pr2 (pr2 (postcomp-cone T f g c)) h = eq-htpy (coherence-square-cone f g c ·r h)

map-standard-pullback-postcomp :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  (T : UU l4) → standard-pullback (postcomp T f) (postcomp T g) → cone f g T
map-standard-pullback-postcomp f g T = tot (λ _ → tot (λ _ → htpy-eq))

abstract
  is-equiv-map-standard-pullback-postcomp :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
    (T : UU l4) → is-equiv (map-standard-pullback-postcomp f g T)
  is-equiv-map-standard-pullback-postcomp f g T =
    is-equiv-tot-is-fiberwise-equiv
      ( λ p → is-equiv-tot-is-fiberwise-equiv (λ q → funext (f ∘ p) (g ∘ q)))

triangle-map-standard-pullback-postcomp :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (T : UU l5) (f : A → X) (g : B → X) (c : cone f g C) →
  cone-map f g c {T} ~
  map-standard-pullback-postcomp f g T ∘
  gap (postcomp T f) (postcomp T g) (postcomp-cone T f g c)
triangle-map-standard-pullback-postcomp T f g c h =
  eq-pair-eq-pr2
    ( eq-pair-eq-pr2
      ( inv (is-section-eq-htpy (coherence-square-cone f g c ·r h))))

abstract
  is-pullback-postcomp-is-pullback :
    {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) → is-pullback f g c →
    (T : UU l5) →
    is-pullback (postcomp T f) (postcomp T g) (postcomp-cone T f g c)
  is-pullback-postcomp-is-pullback f g c is-pb-c T =
    is-equiv-top-map-triangle
      ( cone-map f g c)
      ( map-standard-pullback-postcomp f g T)
      ( gap (f ∘_) (g ∘_) (postcomp-cone T f g c))
      ( triangle-map-standard-pullback-postcomp T f g c)
      ( is-equiv-map-standard-pullback-postcomp f g T)
      ( universal-property-pullback-is-pullback f g c is-pb-c T)

abstract
  is-pullback-is-pullback-postcomp :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    ( {l5 : Level} (T : UU l5) →
      is-pullback (postcomp T f) (postcomp T g) (postcomp-cone T f g c)) →
    is-pullback f g c
  is-pullback-is-pullback-postcomp f g c is-pb-postcomp =
    is-pullback-universal-property-pullback f g c
      ( λ T →
        is-equiv-left-map-triangle
          ( cone-map f g c)
          ( map-standard-pullback-postcomp f g T)
          ( gap (f ∘_) (g ∘_) (postcomp-cone T f g c))
          ( triangle-map-standard-pullback-postcomp T f g c)
          ( is-pb-postcomp T)
          ( is-equiv-map-standard-pullback-postcomp f g T))
```

### Identity types can be presented as pullbacks

Identity types fit into pullback squares

```text
 (x ＝ y) ----> 1
    | ⌟         |
    |           | y
    v           v
    1 --------> A.
          x
```

```agda
module _
  {l : Level} {A : UU l} (x y : A)
  where

  cone-Id : cone (point x) (point y) (x ＝ y)
  pr1 cone-Id = terminal-map (x ＝ y)
  pr1 (pr2 cone-Id) = terminal-map (x ＝ y)
  pr2 (pr2 cone-Id) = id

  inv-gap-cone-Id : standard-pullback (point x) (point y) → x ＝ y
  inv-gap-cone-Id (star , star , p) = p

  abstract
    is-section-inv-gap-cone-Id :
      is-section (gap (point x) (point y) cone-Id) (inv-gap-cone-Id)
    is-section-inv-gap-cone-Id (star , star , p) = refl

  abstract
    is-retraction-inv-gap-cone-Id :
      is-retraction (gap (point x) (point y) cone-Id) (inv-gap-cone-Id)
    is-retraction-inv-gap-cone-Id p = refl

  abstract
    is-pullback-cone-Id : is-pullback (point x) (point y) cone-Id
    is-pullback-cone-Id =
      is-equiv-is-invertible
        ( inv-gap-cone-Id)
        ( is-section-inv-gap-cone-Id)
        ( is-retraction-inv-gap-cone-Id)

module _
  {l : Level} {A : UU l} ((x , y) : A × A)
  where

  cone-Id' : cone (point (x , y)) (diagonal A) (x ＝ y)
  pr1 cone-Id' = terminal-map (x ＝ y)
  pr1 (pr2 cone-Id') = const (x ＝ y) A x
  pr2 (pr2 cone-Id') p = eq-pair-eq-pr2 (inv p)

  inv-gap-cone-Id' :
    standard-pullback (point (x , y)) (diagonal A) → x ＝ y
  inv-gap-cone-Id' (star , z , p) = ap pr1 p ∙ inv (ap pr2 p)

  abstract
    is-section-inv-gap-cone-Id' :
      gap (point (x , y)) (diagonal A) cone-Id' ∘
      inv-gap-cone-Id' ~ id
    is-section-inv-gap-cone-Id' (star , z , refl) = refl

  abstract
    is-retraction-inv-gap-cone-Id' :
      inv-gap-cone-Id' ∘
      gap (point (x , y)) (diagonal A) cone-Id' ~ id
    is-retraction-inv-gap-cone-Id' refl = refl

  abstract
    is-pullback-cone-Id' :
      is-pullback (point (x , y)) (diagonal A) cone-Id'
    is-pullback-cone-Id' =
      is-equiv-is-invertible
        ( inv-gap-cone-Id')
        ( is-section-inv-gap-cone-Id')
        ( is-retraction-inv-gap-cone-Id')
```

### The equivalence on canonical pullbacks induced by parallel cospans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  map-equiv-standard-pullback-htpy :
    standard-pullback f' g' → standard-pullback f g
  map-equiv-standard-pullback-htpy =
    tot (λ a → tot (λ b → concat' (f a) (inv (Hg b)) ∘ concat (Hf a) (g' b)))

  abstract
    is-equiv-map-equiv-standard-pullback-htpy :
      is-equiv map-equiv-standard-pullback-htpy
    is-equiv-map-equiv-standard-pullback-htpy =
      is-equiv-tot-is-fiberwise-equiv
        ( λ a →
          is-equiv-tot-is-fiberwise-equiv
            ( λ b →
              is-equiv-comp
                ( concat' (f a) (inv (Hg b)))
                ( concat (Hf a) (g' b))
                ( is-equiv-concat (Hf a) (g' b))
                ( is-equiv-concat' (f a) (inv (Hg b)))))

  equiv-standard-pullback-htpy :
    standard-pullback f' g' ≃ standard-pullback f g
  pr1 equiv-standard-pullback-htpy = map-equiv-standard-pullback-htpy
  pr2 equiv-standard-pullback-htpy = is-equiv-map-equiv-standard-pullback-htpy
```

### Parallel pullback squares

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  triangle-is-pullback-htpy :
    {c : cone f g C} {c' : cone f' g' C} (Hc : htpy-parallel-cone Hf Hg c c') →
    gap f g c ~ map-equiv-standard-pullback-htpy Hf Hg ∘ gap f' g' c'
  triangle-is-pullback-htpy {p , q , H} {p' , q' , H'} (Hp , Hq , HH) z =
    map-extensionality-standard-pullback f g
      ( Hp z)
      ( Hq z)
      ( ( inv (assoc (ap f (Hp z)) (Hf (p' z) ∙ H' z) (inv (Hg (q' z))))) ∙
        ( inv
          ( right-transpose-eq-concat
            ( H z ∙ ap g (Hq z))
            ( Hg (q' z))
            ( ap f (Hp z) ∙ (Hf (p' z) ∙ H' z))
            ( ( assoc (H z) (ap g (Hq z)) (Hg (q' z))) ∙
              ( HH z) ∙
              ( assoc (ap f (Hp z)) (Hf (p' z)) (H' z))))))

  abstract
    is-pullback-htpy :
      {c : cone f g C} (c' : cone f' g' C)
      (Hc : htpy-parallel-cone Hf Hg c c') →
      is-pullback f' g' c' → is-pullback f g c
    is-pullback-htpy {c} c' H is-pb-c' =
      is-equiv-left-map-triangle
        ( gap f g c)
        ( map-equiv-standard-pullback-htpy Hf Hg)
        ( gap f' g' c')
        ( triangle-is-pullback-htpy H)
        ( is-pb-c')
        ( is-equiv-map-equiv-standard-pullback-htpy Hf Hg)

  abstract
    is-pullback-htpy' :
      (c : cone f g C) {c' : cone f' g' C}
      (Hc : htpy-parallel-cone Hf Hg c c') →
      is-pullback f g c → is-pullback f' g' c'
    is-pullback-htpy' c {c'} H =
      is-equiv-top-map-triangle
        ( gap f g c)
        ( map-equiv-standard-pullback-htpy Hf Hg)
        ( gap f' g' c')
        ( triangle-is-pullback-htpy H)
        ( is-equiv-map-equiv-standard-pullback-htpy Hf Hg)
```

In the following part we will relate the type `htpy-parallel-cone` to the
identity type of cones. Here we will rely on
[function extensionality](foundation-core.function-extensionality.md).

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

  htpy-eq-square :
    (c c' : cone f g C) →
    c ＝ c' → htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c'
  htpy-eq-square c .c refl = refl-htpy-parallel-cone c

  htpy-parallel-cone-refl-htpy-htpy-cone :
    (c c' : cone f g C) → htpy-cone f g c c' →
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
                  ( λ x → ap (_∙ H' x) (inv right-unit)))
                ( is-equiv-concat-htpy
                  ( λ x → ap (H x ∙_) right-unit)
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
      ind-htpy g
        ( λ g'' Hg' →
          (c : cone f g C) →
          is-torsorial (htpy-parallel-cone (refl-htpy' f) Hg' c))
        ( is-torsorial-htpy-parallel-cone-refl-htpy-refl-htpy)

  abstract
    is-torsorial-htpy-parallel-cone :
      {f' : A → X} (Hf : f ~ f') {g' : B → X} (Hg : g ~ g') (c : cone f g C) →
      is-torsorial (htpy-parallel-cone Hf Hg c)
    is-torsorial-htpy-parallel-cone
      {f'} Hf {g'} Hg =
      ind-htpy
        ( f)
        ( λ f'' Hf' → (g' : B → X) (Hg : g ~ g') (c : cone f g C) →
          is-contr (Σ (cone f'' g' C) (htpy-parallel-cone Hf' Hg c)))
        ( λ g' Hg → is-torsorial-htpy-parallel-cone-refl-htpy Hg)
        Hf g' Hg

  tr-tr-refl-htpy-cone :
    (c : cone f g C) →
    let
      tr-c = tr (λ x → cone x g C) (eq-htpy (refl-htpy' f)) c
      tr-tr-c = tr (λ y → cone f y C) (eq-htpy (refl-htpy' g)) tr-c
    in
    tr-tr-c ＝ c
  tr-tr-refl-htpy-cone c =
    let
      tr-c = tr (λ f''' → cone f''' g C) (eq-htpy refl-htpy) c
      tr-tr-c = tr (λ g'' → cone f g'' C) (eq-htpy refl-htpy) tr-c
      α : tr-tr-c ＝ tr-c
      α = ap (λ t → tr (λ g'' → cone f g'' C) t tr-c) (eq-htpy-refl-htpy g)
      β : tr-c ＝ c
      β = ap (λ t → tr (λ f''' → cone f''' g C) t c) (eq-htpy-refl-htpy f)
    in
    α ∙ β

  htpy-eq-square-refl-htpy :
    (c c' : cone f g C) →
    let tr-c = tr (λ x → cone x g C) (eq-htpy (refl-htpy' f)) c
        tr-tr-c = tr (λ y → cone f y C) (eq-htpy (refl-htpy' g)) tr-c
    in
    tr-tr-c ＝ c' → htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c'
  htpy-eq-square-refl-htpy c c' =
    map-inv-is-equiv-precomp-Π-is-equiv
      ( is-equiv-concat (tr-tr-refl-htpy-cone c) c')
      ( λ p → htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c')
      ( htpy-eq-square c c')

  left-map-triangle-eq-square-refl-htpy :
    (c c' : cone f g C) →
    htpy-eq-square-refl-htpy c c' ∘ concat (tr-tr-refl-htpy-cone c) c' ~
    htpy-eq-square c c'
  left-map-triangle-eq-square-refl-htpy c c' =
    is-section-map-inv-is-equiv-precomp-Π-is-equiv
      ( is-equiv-concat (tr-tr-refl-htpy-cone c) c')
      ( λ p → htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c')
      ( htpy-eq-square c c')

  abstract
    htpy-parallel-cone-eq' :
      {g' : B → X} (Hg : g ~ g') →
      (c : cone f g C) (c' : cone f g' C) →
      let
        tr-c = tr (λ x → cone x g C) (eq-htpy (refl-htpy' f)) c
        tr-tr-c = tr (λ y → cone f y C) (eq-htpy Hg) tr-c
      in
      tr-tr-c ＝ c' → htpy-parallel-cone (refl-htpy' f) Hg c c'
    htpy-parallel-cone-eq' =
      ind-htpy g
        ( λ g'' Hg' →
          ( c : cone f g C) (c' : cone f g'' C) →
          Id
            ( tr
              ( λ g'' → cone f g'' C)
              ( eq-htpy Hg')
              ( tr (λ f''' → cone f''' g C) (eq-htpy (refl-htpy' f)) c))
            ( c') →
          htpy-parallel-cone refl-htpy Hg' c c')
        ( htpy-eq-square-refl-htpy)

    left-map-triangle-parallel-cone-eq' :
      (c c' : cone f g C) →
      ( ( htpy-parallel-cone-eq' refl-htpy c c') ∘
        ( concat (tr-tr-refl-htpy-cone c) c')) ~
      ( htpy-eq-square c c')
    left-map-triangle-parallel-cone-eq' c c' =
      ( htpy-right-whisker
        ( multivariable-htpy-eq 3
          ( compute-ind-htpy g
            ( λ g'' Hg' →
              ( c : cone f g C) (c' : cone f g'' C) →
              ( tr
                ( λ g'' → cone f g'' C)
                ( eq-htpy Hg')
                ( tr (λ f''' → cone f''' g C) (eq-htpy (refl-htpy' f)) c)) ＝
              ( c') →
              htpy-parallel-cone refl-htpy Hg' c c')
            ( htpy-eq-square-refl-htpy))
          ( c)
          ( c'))
        ( concat (tr-tr-refl-htpy-cone c) c')) ∙h
      ( left-map-triangle-eq-square-refl-htpy c c')

  abstract
    htpy-parallel-cone-eq :
      {f' : A → X} (Hf : f ~ f') {g' : B → X} (Hg : g ~ g') →
      (c : cone f g C) (c' : cone f' g' C) →
      let tr-c = tr (λ x → cone x g C) (eq-htpy Hf) c
          tr-tr-c = tr (λ y → cone f' y C) (eq-htpy Hg) tr-c
      in
      tr-tr-c ＝ c' → htpy-parallel-cone Hf Hg c c'
    htpy-parallel-cone-eq {f'} Hf {g'} Hg c c' p =
      ind-htpy f
      ( λ f'' Hf' →
        ( g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f'' g' C) →
        ( Id
          ( tr (λ g'' → cone f'' g'' C) (eq-htpy Hg)
            ( tr (λ f''' → cone f''' g C) (eq-htpy Hf') c))
          ( c')) →
        htpy-parallel-cone Hf' Hg c c')
      ( λ g' → htpy-parallel-cone-eq' {g' = g'})
      Hf g' Hg c c' p

    left-map-triangle-parallel-cone-eq :
      (c c' : cone f g C) →
      ( htpy-parallel-cone-eq refl-htpy refl-htpy c c') ∘
        ( concat (tr-tr-refl-htpy-cone c) c') ~
      ( htpy-eq-square c c')
    left-map-triangle-parallel-cone-eq c c' =
      ( htpy-right-whisker
        ( multivariable-htpy-eq 5
          ( compute-ind-htpy f
            ( λ f'' Hf' →
              ( g' : B → X) (Hg : g ~ g')
              (c : cone f g C) (c' : cone f'' g' C) →
              ( tr
                  ( λ g'' → cone f'' g'' C)
                  ( eq-htpy Hg)
                  ( tr (λ f''' → cone f''' g C) (eq-htpy Hf') c) ＝
                ( c')) →
              htpy-parallel-cone Hf' Hg c c')
            ( λ g' → htpy-parallel-cone-eq' {g' = g'}))
          ( g)
          ( refl-htpy)
          ( c)
          ( c'))
        ( concat (tr-tr-refl-htpy-cone c) c')) ∙h
      ( left-map-triangle-parallel-cone-eq' c c')

  abstract
    is-fiberwise-equiv-htpy-parallel-cone-eq :
      {f' : A → X} (Hf : f ~ f') {g' : B → X} (Hg : g ~ g') →
      (c : cone f g C) (c' : cone f' g' C) →
      is-equiv (htpy-parallel-cone-eq Hf Hg c c')
    is-fiberwise-equiv-htpy-parallel-cone-eq {f'} Hf {g'} Hg c c' =
      ind-htpy f
        ( λ f' Hf →
          ( g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f' g' C) →
            is-equiv (htpy-parallel-cone-eq Hf Hg c c'))
        ( λ g' Hg c c' →
          ind-htpy g
            ( λ g' Hg →
              ( c : cone f g C) (c' : cone f g' C) →
                is-equiv (htpy-parallel-cone-eq refl-htpy Hg c c'))
            ( λ c c' →
              is-equiv-right-map-triangle
                ( htpy-eq-square c c')
                ( htpy-parallel-cone-eq refl-htpy refl-htpy c c')
                ( concat (tr-tr-refl-htpy-cone c) c')
                ( inv-htpy (left-map-triangle-parallel-cone-eq c c'))
                ( fundamental-theorem-id
                  ( is-torsorial-htpy-parallel-cone
                    ( refl-htpy' f)
                    ( refl-htpy' g)
                    ( c))
                  ( htpy-eq-square c) c')
                ( is-equiv-concat (tr-tr-refl-htpy-cone c) c'))
            Hg c c')
        Hf g' Hg c c'

  eq-htpy-parallel-cone :
    {f' : A → X} (Hf : f ~ f') {g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f' g' C) →
    let
      tr-c = tr (λ x → cone x g C) (eq-htpy Hf) c
      tr-tr-c = tr (λ y → cone f' y C) (eq-htpy Hg) tr-c
    in
    htpy-parallel-cone Hf Hg c c' → tr-tr-c ＝ c'
  eq-htpy-parallel-cone Hf Hg c c' =
    map-inv-is-equiv (is-fiberwise-equiv-htpy-parallel-cone-eq Hf Hg c c')
```

### Dependent products of pullbacks are pullbacks

Given a family of pullback squares, their dependent product is again a pullback
square.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  where

  map-standard-pullback-Π :
    standard-pullback (map-Π f) (map-Π g) →
    (i : I) → standard-pullback (f i) (g i)
  pr1 (map-standard-pullback-Π (α , β , γ) i) = α i
  pr1 (pr2 (map-standard-pullback-Π (α , β , γ) i)) = β i
  pr2 (pr2 (map-standard-pullback-Π (α , β , γ) i)) = htpy-eq γ i

  inv-map-standard-pullback-Π :
    ((i : I) → standard-pullback (f i) (g i)) →
    standard-pullback (map-Π f) (map-Π g)
  pr1 (inv-map-standard-pullback-Π h) i = pr1 (h i)
  pr1 (pr2 (inv-map-standard-pullback-Π h)) i = pr1 (pr2 (h i))
  pr2 (pr2 (inv-map-standard-pullback-Π h)) = eq-htpy (λ i → pr2 (pr2 (h i)))

  abstract
    is-section-inv-map-standard-pullback-Π :
      is-section (map-standard-pullback-Π) (inv-map-standard-pullback-Π)
    is-section-inv-map-standard-pullback-Π h =
      eq-htpy
        ( λ i →
          map-extensionality-standard-pullback (f i) (g i) refl refl
            ( inv
              ( ( right-unit) ∙
                ( htpy-eq (is-section-eq-htpy (λ i → pr2 (pr2 (h i)))) i))))

  abstract
    is-retraction-inv-map-standard-pullback-Π :
      is-retraction (map-standard-pullback-Π) (inv-map-standard-pullback-Π)
    is-retraction-inv-map-standard-pullback-Π (α , β , γ) =
      map-extensionality-standard-pullback
        ( map-Π f)
        ( map-Π g)
        ( refl)
        ( refl)
        ( inv (right-unit ∙ is-retraction-eq-htpy γ))

  abstract
    is-equiv-map-standard-pullback-Π :
      is-equiv (map-standard-pullback-Π)
    is-equiv-map-standard-pullback-Π =
      is-equiv-is-invertible
        ( inv-map-standard-pullback-Π)
        ( is-section-inv-map-standard-pullback-Π)
        ( is-retraction-inv-map-standard-pullback-Π)

module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  (c : (i : I) → cone (f i) (g i) (C i))
  where

  cone-Π : cone (map-Π f) (map-Π g) ((i : I) → C i)
  pr1 cone-Π = map-Π (λ i → pr1 (c i))
  pr1 (pr2 cone-Π) = map-Π (λ i → pr1 (pr2 (c i)))
  pr2 (pr2 cone-Π) = htpy-map-Π (λ i → pr2 (pr2 (c i)))

  triangle-map-standard-pullback-Π :
    map-Π (λ i → gap (f i) (g i) (c i)) ~
    map-standard-pullback-Π f g ∘ gap (map-Π f) (map-Π g) cone-Π
  triangle-map-standard-pullback-Π h =
    eq-htpy
      ( λ i →
        map-extensionality-standard-pullback
          ( f i)
          ( g i)
          ( refl)
          ( refl)
          ( htpy-eq (is-section-eq-htpy _) i ∙ inv right-unit))

  abstract
    is-pullback-Π :
      ((i : I) → is-pullback (f i) (g i) (c i)) →
      is-pullback (map-Π f) (map-Π g) cone-Π
    is-pullback-Π is-pb-c =
      is-equiv-top-map-triangle
        ( map-Π (λ i → gap (f i) (g i) (c i)))
        ( map-standard-pullback-Π f g)
        ( gap (map-Π f) (map-Π g) cone-Π)
        ( triangle-map-standard-pullback-Π)
        ( is-equiv-map-standard-pullback-Π f g)
        ( is-equiv-map-Π-is-fiberwise-equiv is-pb-c)
```

### Coproducts of pullbacks are pullbacks

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  map-coprod-cone-inl :
    standard-pullback f g →
    standard-pullback (map-coprod f f') (map-coprod g g')
  pr1 (map-coprod-cone-inl (x , y , p)) = inl x
  pr1 (pr2 (map-coprod-cone-inl (x , y , p))) = inl y
  pr2 (pr2 (map-coprod-cone-inl (x , y , p))) = ap inl p

  map-coprod-cone-inr :
    standard-pullback f' g' →
    standard-pullback (map-coprod f f') (map-coprod g g')
  pr1 (map-coprod-cone-inr (x , y , p)) = inr x
  pr1 (pr2 (map-coprod-cone-inr (x , y , p))) = inr y
  pr2 (pr2 (map-coprod-cone-inr (x , y , p))) = ap inr p

  map-coprod-cone :
    standard-pullback f g + standard-pullback f' g' →
    standard-pullback (map-coprod f f') (map-coprod g g')
  map-coprod-cone (inl v) = map-coprod-cone-inl v
  map-coprod-cone (inr u) = map-coprod-cone-inr u

  map-inv-coprod-cone :
    standard-pullback (map-coprod f f') (map-coprod g g') →
    standard-pullback f g + standard-pullback f' g'
  map-inv-coprod-cone (inl x , inl y , p) = inl (x , y , is-injective-inl p)
  map-inv-coprod-cone (inr x , inr y , p) = inr (x , y , is-injective-inr p)

  is-section-map-inv-coprod-cone :
    is-section map-coprod-cone map-inv-coprod-cone
  is-section-map-inv-coprod-cone (inl x , inl y , p) =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 (is-section-is-injective-inl p))
  is-section-map-inv-coprod-cone (inr x , inr y , p) =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 (is-section-is-injective-inr p))

  is-retraction-map-inv-coprod-cone :
    is-retraction map-coprod-cone map-inv-coprod-cone
  is-retraction-map-inv-coprod-cone (inl (x , y , p)) =
    ap inl (eq-pair-eq-pr2 (eq-pair-eq-pr2 (is-retraction-is-injective-inl p)))
  is-retraction-map-inv-coprod-cone (inr (x , y , p)) =
    ap inr (eq-pair-eq-pr2 (eq-pair-eq-pr2 (is-retraction-is-injective-inr p)))

  abstract
    is-equiv-map-coprod-cone : is-equiv map-coprod-cone
    is-equiv-map-coprod-cone =
      is-equiv-is-invertible
        map-inv-coprod-cone
        is-section-map-inv-coprod-cone
        is-retraction-map-inv-coprod-cone
```

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  coprod-cone :
    cone f g C → cone f' g' C' →
    cone (map-coprod f f') (map-coprod g g') (C + C')
  pr1 (coprod-cone (p , q , H) (p' , q' , H')) = map-coprod p p'
  pr1 (pr2 (coprod-cone (p , q , H) (p' , q' , H'))) = map-coprod q q'
  pr2 (pr2 (coprod-cone (p , q , H) (p' , q' , H'))) =
    ( inv-htpy (preserves-comp-map-coprod p f p' f')) ∙h
    ( htpy-map-coprod H H') ∙h
    ( preserves-comp-map-coprod q g q' g')

  triangle-map-coprod-cone :
    (c : cone f g C) (c' : cone f' g' C') →
    gap (map-coprod f f') (map-coprod g g') (coprod-cone c c') ~
    map-coprod-cone f g f' g' ∘ map-coprod (gap f g c) (gap f' g' c')
  triangle-map-coprod-cone c c' (inl _) =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 right-unit)
  triangle-map-coprod-cone c c' (inr _) =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 right-unit)

  abstract
    is-pullback-coprod-is-pullback-pair :
      (c : cone f g C) (c' : cone f' g' C') →
      is-pullback f g c → is-pullback f' g' c' →
      is-pullback (map-coprod f f') (map-coprod g g') (coprod-cone c c')
    is-pullback-coprod-is-pullback-pair c c' is-pb-c is-pb-c' =
      is-equiv-left-map-triangle
        ( gap (map-coprod f f') (map-coprod g g') (coprod-cone c c'))
        ( map-coprod-cone f g f' g')
        ( map-coprod (gap f g c) (gap f' g' c'))
        ( triangle-map-coprod-cone c c')
        ( is-equiv-map-coprod is-pb-c is-pb-c')
        ( is-equiv-map-coprod-cone f g f' g')
```

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : A → C} {h : B → D} {k : C → D}
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  {f' : A' → B'} {g' : A' → C'} {h' : B' → D'} {k' : C' → D'}
  {hA : A' → A} {hB : B' → B} {hC : C' → C} {hD : D' → D}
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom)
  where

  is-pullback-back-left-is-pullback-back-right-cube :
    is-pullback h hD (hB , h' , front-left) →
    is-pullback k hD (hC , k' , front-right) →
    is-pullback g hC (hA , g' , back-right) →
    is-pullback f hB (hA , f' , back-left)
  is-pullback-back-left-is-pullback-back-right-cube
    is-pb-front-left is-pb-front-right is-pb-back-right =
    is-pullback-left-square-is-pullback-rectangle f h hD
      ( hB , h' , front-left)
      ( hA , f' , back-left)
      ( is-pb-front-left)
      ( is-pullback-htpy
        ( bottom)
        ( refl-htpy)
        ( triple
          ( hA)
          ( k' ∘ g')
          ( rectangle-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom))
        ( triple
          ( refl-htpy)
          ( top)
          ( coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c))
        ( is-pullback-rectangle-is-pullback-left-square g k hD
          ( hC , k' , front-right)
          ( hA , g' , back-right)
          ( is-pb-front-right)
          ( is-pb-back-right)))

  is-pullback-back-right-is-pullback-back-left-cube :
    is-pullback h hD (hB , h' , front-left) →
    is-pullback k hD (hC , k' , front-right) →
    is-pullback f hB (hA , f' , back-left) →
    is-pullback g hC (hA , g' , back-right)
  is-pullback-back-right-is-pullback-back-left-cube
    is-pb-front-left is-pb-front-right is-pb-back-left =
    is-pullback-left-square-is-pullback-rectangle g k hD
      ( hC , k' , front-right)
      ( hA , g' , back-right)
      ( is-pb-front-right)
      ( is-pullback-htpy'
        ( bottom)
        ( refl-htpy)
        ( triple
          ( hA)
          ( h' ∘ f')
          ( rectangle-left-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom))
        ( triple
          ( refl-htpy)
          ( top)
          ( coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c))
        ( is-pullback-rectangle-is-pullback-left-square f h hD
          ( hB , h' , front-left)
          ( hA , f' , back-left)
          ( is-pb-front-left)
          ( is-pb-back-left)))
```

### In a commuting cube where the vertical maps are equivalences, the bottom square is a pullback if and only if the top square is a pullback

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom)
  where

  is-pullback-bottom-is-pullback-top-cube-is-equiv :
    is-equiv hA → is-equiv hB → is-equiv hC → is-equiv hD →
    is-pullback h' k' (f' , g' , top) →
    is-pullback h k (f , g , bottom)
  is-pullback-bottom-is-pullback-top-cube-is-equiv
    is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-top =
    descent-is-equiv hB h k
      ( f , g , bottom)
      ( f' , hA , inv-htpy (back-left))
      ( is-equiv-hB)
      ( is-equiv-hA)
      ( is-pullback-htpy
        ( front-left)
        ( refl-htpy' k)
        ( triple
          ( f')
          ( hC ∘ g')
          ( rectangle-top-front-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom))
        ( triple
          ( refl-htpy' f')
          ( back-right)
          ( coherence-htpy-parallel-cone-coherence-cube-maps
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c))
        ( is-pullback-rectangle-is-pullback-left-square
          ( h')
          ( hD)
          ( k)
          ( k' , hC , inv-htpy front-right)
          ( f' , g' , top)
          ( is-pullback-is-equiv-horizontal-maps hD k
            ( k' , hC , inv-htpy front-right)
            ( is-equiv-hD)
            ( is-equiv-hC))
          ( is-pb-top)))

  is-pullback-top-is-pullback-bottom-cube-is-equiv :
    is-equiv hA → is-equiv hB → is-equiv hC → is-equiv hD →
    is-pullback h k (f , g , bottom) →
    is-pullback h' k' (f' , g' , top)
  is-pullback-top-is-pullback-bottom-cube-is-equiv
    is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-bottom =
    is-pullback-top-is-pullback-rectangle h hD k'
      ( hB , h' , front-left)
      ( f' , g' , top)
      ( is-pullback-is-equiv-vertical-maps h hD
        ( hB , h' , front-left)
        is-equiv-hD is-equiv-hB)
      ( is-pullback-htpy' refl-htpy front-right
        ( pasting-vertical-cone h k hC
          ( f , g , bottom)
          ( hA , g' , back-right))
        ( triple
          ( back-left)
          ( refl-htpy)
          ( ( assoc-htpy
              ( bottom ·r hA)
              ( k ·l back-right)
              ( front-right ·r g')) ∙h
            ( inv-htpy c) ∙h
            ( assoc-htpy (h ·l back-left) (front-left ·r f') (hD ·l top)) ∙h
            ( ap-concat-htpy'
              ( (front-left ·r f') ∙h (hD ·l top))
              ( inv-htpy-right-unit-htpy {H = h ·l back-left}))))
        ( is-pullback-rectangle-is-pullback-top h k hC
          ( f , g , bottom)
          ( hA , g' , back-right)
          ( is-pb-bottom)
          ( is-pullback-is-equiv-vertical-maps g hC
            ( hA , g' , back-right)
            is-equiv-hC is-equiv-hA)))
```

### In a commuting cube where the maps from back-right to front-left are equivalences, the back-right square is a pullback if and only if the front-left square is a pullback

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom)
  where

  is-pullback-front-left-is-pullback-back-right-cube-is-equiv :
    is-equiv f' → is-equiv f → is-equiv k' → is-equiv k →
    is-pullback g hC (hA , g' , back-right) →
    is-pullback h hD (hB , h' , front-left)
  is-pullback-front-left-is-pullback-back-right-cube-is-equiv
    is-equiv-f' is-equiv-f is-equiv-k' is-equiv-k is-pb-back-right =
    is-pullback-bottom-is-pullback-top-cube-is-equiv
      hB h' h hD hA g' g hC f' f k' k
      back-right (inv-htpy back-left) top bottom (inv-htpy front-right)
      ( front-left)
      ( coherence-cube-maps-mirror-B f g h k f' g' h' k' hA hB hC hD top
        back-left back-right front-left front-right bottom c)
      is-equiv-f' is-equiv-f is-equiv-k' is-equiv-k is-pb-back-right

  is-pullback-front-right-is-pullback-back-left-cube-is-equiv :
    is-equiv g' → is-equiv h' → is-equiv g → is-equiv h →
    is-pullback f hB (hA , f' , back-left) →
    is-pullback k hD (hC , k' , front-right)
  is-pullback-front-right-is-pullback-back-left-cube-is-equiv
    is-equiv-g' is-equiv-h' is-equiv-g is-equiv-h is-pb-back-left =
    is-pullback-bottom-is-pullback-top-cube-is-equiv
      hC k' k hD hA f' f hB g' g h' h
      back-left (inv-htpy back-right) (inv-htpy top)
      ( inv-htpy bottom) (inv-htpy front-left) front-right
      ( coherence-cube-maps-rotate-120 f g h k f' g' h' k' hA hB hC hD
        top back-left back-right front-left front-right bottom c)
      is-equiv-g' is-equiv-g is-equiv-h' is-equiv-h is-pb-back-left
```

### Identity types commute with pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  cone-ap :
    (c1 c2 : C) →
    cone
      ( λ (α : vertical-map-cone f g c c1 ＝ vertical-map-cone f g c c2) →
        ap f α ∙ coherence-square-cone f g c c2)
      ( λ (β : horizontal-map-cone f g c c1 ＝ horizontal-map-cone f g c c2) →
        coherence-square-cone f g c c1 ∙ ap g β)
      ( c1 ＝ c2)
  pr1 (cone-ap c1 c2) = ap (vertical-map-cone f g c)
  pr1 (pr2 (cone-ap c1 c2)) = ap (horizontal-map-cone f g c)
  pr2 (pr2 (cone-ap c1 c2)) γ =
    ( ap
      ( _∙ coherence-square-cone f g c c2)
      ( inv (ap-comp f (vertical-map-cone f g c) γ))) ∙
    ( ( inv-nat-htpy (coherence-square-cone f g c) γ) ∙
      ( ap
        ( coherence-square-cone f g c c1 ∙_)
        ( ap-comp g (horizontal-map-cone f g c) γ)))

  cone-ap' :
    (c1 c2 : C) →
    cone
      ( λ (α : vertical-map-cone f g c c1 ＝ vertical-map-cone f g c c2) →
        tr
          ( f (vertical-map-cone f g c c1) ＝_)
          ( coherence-square-cone f g c c2)
          ( ap f α))
      ( λ (β : horizontal-map-cone f g c c1 ＝ horizontal-map-cone f g c c2) →
        coherence-square-cone f g c c1 ∙ ap g β)
      ( c1 ＝ c2)
  pr1 (cone-ap' c1 c2) = ap (vertical-map-cone f g c)
  pr1 (pr2 (cone-ap' c1 c2)) = ap (horizontal-map-cone f g c)
  pr2 (pr2 (cone-ap' c1 c2)) γ =
    ( tr-Id-right
      ( coherence-square-cone f g c c2)
      ( ap f (ap (vertical-map-cone f g c) γ))) ∙
    ( ( ap
        ( _∙ coherence-square-cone f g c c2)
        ( inv (ap-comp f (vertical-map-cone f g c) γ))) ∙
      ( ( inv-nat-htpy (coherence-square-cone f g c) γ) ∙
        ( ap
          ( coherence-square-cone f g c c1 ∙_)
          ( ap-comp g (horizontal-map-cone f g c) γ))))

  is-pullback-cone-ap :
    is-pullback f g c →
    (c1 c2 : C) →
    is-pullback
      ( λ (α : vertical-map-cone f g c c1 ＝ vertical-map-cone f g c c2) →
        ap f α ∙ coherence-square-cone f g c c2)
      ( λ (β : horizontal-map-cone f g c c1 ＝ horizontal-map-cone f g c c2) →
        coherence-square-cone f g c c1 ∙ ap g β)
      ( cone-ap c1 c2)
  is-pullback-cone-ap is-pb-c c1 c2 =
    is-pullback-htpy'
      ( λ α → tr-Id-right (coherence-square-cone f g c c2) (ap f α))
      ( refl-htpy)
      ( cone-ap' c1 c2)
      ( refl-htpy , refl-htpy , right-unit-htpy)
      ( is-pullback-family-is-pullback-tot
        ( f (vertical-map-cone f g c c1) ＝_)
        ( λ a → ap f {x = vertical-map-cone f g c c1} {y = a})
        ( λ b β → coherence-square-cone f g c c1 ∙ ap g β)
        ( c)
        ( cone-ap' c1)
        ( is-pb-c)
        ( is-pullback-is-equiv-vertical-maps
          ( map-Σ _ f (λ a α → ap f α))
          ( map-Σ _ g (λ b β → coherence-square-cone f g c c1 ∙ ap g β))
          ( tot-cone-cone-family
            ( f (vertical-map-cone f g c c1) ＝_)
            ( λ a → ap f)
            ( λ b β → coherence-square-cone f g c c1 ∙ ap g β)
            ( c)
            ( cone-ap' c1))
          ( is-equiv-is-contr _
            ( is-torsorial-path (horizontal-map-cone f g c c1))
            ( is-torsorial-path (f (vertical-map-cone f g c c1))))
          ( is-equiv-is-contr _
            ( is-torsorial-path c1)
            ( is-torsorial-path (vertical-map-cone f g c c1))))
        ( c2))
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
