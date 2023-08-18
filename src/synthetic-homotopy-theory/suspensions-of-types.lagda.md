# Suspensions of types

```agda
module synthetic-homotopy-theory.suspensions-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.conjugation-loops
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Definition

### Suspension structure

```agda
module _
  {l1 l2 : Level} (X : UU l1) (Y : UU l2)
  where

  suspension-structure : UU (l1 ⊔ l2)
  suspension-structure = Σ Y (λ N → Σ Y (λ S → (x : X) → N ＝ S))

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  N-suspension-structure : suspension-structure X Y → Y
  N-suspension-structure c = pr1 c

  S-suspension-structure : suspension-structure X Y → Y
  S-suspension-structure c = (pr1 ∘ pr2) c

  merid-suspension-structure :
    (c : suspension-structure X Y) →
    X → N-suspension-structure c ＝ S-suspension-structure c
  merid-suspension-structure c = (pr2 ∘ pr2) c
```

### Suspension cocones on a type

```agda
suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
suspension-cocone X Y = cocone (const X unit star) (const X unit star) Y

cocone-suspension-structure :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) →
  suspension-structure X Y → suspension-cocone X Y
cocone-suspension-structure X Y (pair N (pair S merid)) =
  pair
    ( const unit Y N)
    ( pair
      ( const unit Y S)
      ( merid))
```

### The universal property of the suspension of a type `X`

```agda
universal-property-suspension' :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2)
  (susp-str : suspension-structure X Y) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-suspension' l X Y susp-str-Y =
  universal-property-pushout l
    ( const X unit star)
    ( const X unit star)
    ( cocone-suspension-structure X Y susp-str-Y)

is-suspension :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
is-suspension l X Y =
  Σ (suspension-structure X Y) (universal-property-suspension' l X Y)
```

### The suspension of an ordinary type `X`

```agda
suspension :
  {l : Level} → UU l → UU l
suspension X = pushout (const X unit star) (const X unit star)

N-susp :
  {l : Level} {X : UU l} → suspension X
N-susp {X = X} = inl-pushout (const X unit star) (const X unit star) star

S-susp :
  {l : Level} {X : UU l} → suspension X
S-susp {X = X} = inr-pushout (const X unit star) (const X unit star) star

merid-susp :
  {l : Level} {X : UU l} → X → Id (N-susp {X = X}) (S-susp {X = X})
merid-susp {X = X} = glue-pushout (const X unit star) (const X unit star)

suspension-structure-suspension :
  {l : Level} (X : UU l) → suspension-structure X (suspension X)
pr1 (suspension-structure-suspension X) = N-susp
pr1 (pr2 (suspension-structure-suspension X)) = S-susp
pr2 (pr2 (suspension-structure-suspension X)) = merid-susp
```

### The suspension of a pointed type

```agda
suspension-Pointed-Type :
  {l : Level} → Pointed-Type l → Pointed-Type l
pr1 (suspension-Pointed-Type X) = suspension (type-Pointed-Type X)
pr2 (suspension-Pointed-Type X) = N-susp
```

#### Suspension structure induced by a pointed type

```agda
constant-suspension-structure-Pointed-Type :
  {l1 l2 : Level} (X : UU l1) (Y : Pointed-Type l2) →
  suspension-structure X (type-Pointed-Type Y)
pr1 (constant-suspension-structure-Pointed-Type X Y) =
  point-Pointed-Type Y
pr1 (pr2 (constant-suspension-structure-Pointed-Type X Y)) =
  point-Pointed-Type Y
pr2 (pr2 (constant-suspension-structure-Pointed-Type X Y)) =
  const X (point-Pointed-Type Y ＝ point-Pointed-Type Y) refl
```

## Properties

#### Characterization of equalities in `suspension-structure`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2}
  where

  htpy-suspension-structure :
    (c c' : suspension-structure X Z) → UU (l1 ⊔ l2)
  htpy-suspension-structure c c' =
    Σ ( (N-suspension-structure c) ＝ (N-suspension-structure c'))
      ( λ p →
        Σ ( ( S-suspension-structure c) ＝ ( S-suspension-structure c'))
          ( λ q →
            ( x : X) →
            ( merid-suspension-structure c x ∙ q) ＝
            ( p ∙ merid-suspension-structure c' x)))

  extensionality-suspension-structure :
    (c c' : suspension-structure X Z) →
    (c ＝ c') ≃ (htpy-suspension-structure c c')
  extensionality-suspension-structure (N , S , merid) =
    extensionality-Σ
      ( λ y p →
        Σ (S ＝ pr1 y) (λ q → (x : X) → (merid x ∙ q) ＝ (p ∙ pr2 y x)))
      ( refl)
      ( refl , right-unit-htpy)
      ( λ z → id-equiv)
      ( extensionality-Σ
        ( λ H q → (x : X) → (merid x ∙ q) ＝ H x)
        ( refl)
        ( right-unit-htpy)
        ( λ z → id-equiv)
        ( λ H → equiv-concat-htpy right-unit-htpy H ∘e equiv-funext))

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} {c c' : suspension-structure X Z}
  where

  htpy-eq-suspension-structure : (c ＝ c') → htpy-suspension-structure c c'
  htpy-eq-suspension-structure =
    map-equiv (extensionality-suspension-structure c c')

  eq-htpy-suspension-structure : htpy-suspension-structure c c' → (c ＝ c')
  eq-htpy-suspension-structure =
    map-inv-equiv (extensionality-suspension-structure c c')

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} {c : suspension-structure X Z}
  where

  refl-htpy-suspension-structure : htpy-suspension-structure c c
  refl-htpy-suspension-structure = refl , (refl , right-unit-htpy)

  is-refl-refl-htpy-suspension-structure :
    refl-htpy-suspension-structure ＝ htpy-eq-suspension-structure refl
  is-refl-refl-htpy-suspension-structure = refl

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} {c : suspension-structure X Z}
  where

  ind-htpy-suspension-structure :
    { l : Level}
    ( P :
      ( c' : suspension-structure X Z) →
      ( htpy-suspension-structure c c') →
      UU l) →
    ( P c refl-htpy-suspension-structure) →
    ( ( c' : suspension-structure X Z)
      ( H : htpy-suspension-structure c c') →
      P c' H)
  ind-htpy-suspension-structure P =
    pr1
      ( Ind-identity-system
        ( c)
        ( refl-htpy-suspension-structure)
        ( is-contr-equiv
          ( Σ (suspension-structure X Z) (λ c' → c ＝ c'))
          ( inv-equiv
            ( equiv-tot (extensionality-suspension-structure c)))
          ( is-contr-total-path c))
        ( P))
```

#### The action of paths of the projections have the expected effect

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} (c : suspension-structure X Z)
  where

  ap-pr1-eq-htpy-suspension-structure :
    (c' : suspension-structure X Z) (H : htpy-suspension-structure c c') →
    (ap (pr1) (eq-htpy-suspension-structure H)) ＝ (pr1 H)
  ap-pr1-eq-htpy-suspension-structure =
    ind-htpy-suspension-structure
      ( λ c' H → (ap (pr1) (eq-htpy-suspension-structure H)) ＝ (pr1 H))
      ( (ap
        ( ap pr1)
        ( is-retraction-map-inv-equiv
          ( extensionality-suspension-structure c c)
          ( refl))))

  ap-pr1∘pr2-eq-htpy-suspension-structure :
    (c' : suspension-structure X Z) (H : htpy-suspension-structure c c') →
    (ap (pr1 ∘ pr2) (eq-htpy-suspension-structure H)) ＝ ((pr1 ∘ pr2) H)
  ap-pr1∘pr2-eq-htpy-suspension-structure =
    ind-htpy-suspension-structure
      ( λ c' H →
        ap (pr1 ∘ pr2) (eq-htpy-suspension-structure H) ＝ (pr1 ∘ pr2) H)
      ( ap
        ( ap (pr1 ∘ pr2))
        ( is-retraction-map-inv-equiv
          ( extensionality-suspension-structure c c)
          ( refl)))
```

### The universal property of the suspension as a pushout

```agda
ev-suspension :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (susp-str-Y : suspension-structure X Y) →
  (Z : UU l3) → (Y → Z) → suspension-structure X Z
ev-suspension (pair N (pair S merid)) Z h =
  pair (h N) (pair (h S) (h ·l merid))

universal-property-suspension :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) →
  suspension-structure X Y → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-suspension l X Y susp-str-Y =
  (Z : UU l) → is-equiv (ev-suspension susp-str-Y Z)

comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-cocone X Z ≃ suspension-structure X Z
comparison-suspension-cocone X Z =
  equiv-Σ
    ( λ z1 → Σ Z (λ z2 → (x : X) → Id z1 z2))
    ( equiv-universal-property-unit Z)
    ( λ z1 →
      equiv-Σ
        ( λ z2 → (x : X) → Id (z1 star) z2)
        ( equiv-universal-property-unit Z)
        ( λ z2 → id-equiv))

map-comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-cocone X Z → suspension-structure X Z
map-comparison-suspension-cocone X Z =
  map-equiv (comparison-suspension-cocone X Z)

is-equiv-map-comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  is-equiv (map-comparison-suspension-cocone X Z)
is-equiv-map-comparison-suspension-cocone X Z =
  is-equiv-map-equiv (comparison-suspension-cocone X Z)

triangle-ev-suspension :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (susp-str-Y : suspension-structure X Y) →
  (Z : UU l3) →
  ( ( map-comparison-suspension-cocone X Z) ∘
    ( cocone-map
      ( const X unit star)
      ( const X unit star)
      ( cocone-suspension-structure X Y susp-str-Y))) ~
  ( ev-suspension susp-str-Y Z)
triangle-ev-suspension (pair N (pair S merid)) Z h = refl

is-equiv-ev-suspension :
  { l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  ( susp-str-Y : suspension-structure X Y) →
  ( up-Y : universal-property-suspension' l3 X Y susp-str-Y) →
  ( Z : UU l3) → is-equiv (ev-suspension susp-str-Y Z)
is-equiv-ev-suspension {X = X} susp-str-Y up-Y Z =
  is-equiv-comp-htpy
    ( ev-suspension susp-str-Y Z)
    ( map-comparison-suspension-cocone X Z)
    ( cocone-map
      ( const X unit star)
      ( const X unit star)
      ( cocone-suspension-structure X _ susp-str-Y))
    ( inv-htpy (triangle-ev-suspension susp-str-Y Z))
    ( up-Y Z)
    ( is-equiv-map-comparison-suspension-cocone X Z)
```

### The suspension of X has the universal property of suspensions

```agda
module _
  {l1 : Level} (X : UU l1)
  where

  up-suspension :
    {l : Level} →
    universal-property-suspension l X
      ( suspension X)
      ( suspension-structure-suspension X)
  up-suspension Z =
    is-equiv-htpy
      ( ev-suspension (suspension-structure-suspension X) Z)
      ( triangle-ev-suspension
        { X = X}
        { Y = suspension X}
        ( suspension-structure-suspension X) Z)
      ( is-equiv-map-equiv
        ( ( comparison-suspension-cocone X Z) ∘e
          ( equiv-up-pushout (const X unit star) (const X unit star) Z)))

  equiv-up-suspension :
    {l : Level} (Z : UU l) → (suspension X → Z) ≃ (suspension-structure X Z)
  pr1 (equiv-up-suspension Z) =
    ev-suspension (suspension-structure-suspension X) Z
  pr2 (equiv-up-suspension Z) = up-suspension Z

  map-inv-up-suspension :
    {l : Level} (Z : UU l) → suspension-structure X Z → suspension X → Z
  map-inv-up-suspension Z =
    map-inv-equiv (equiv-up-suspension Z)

  is-section-map-inv-up-suspension :
    {l : Level} (Z : UU l) →
    ( ( ev-suspension ((suspension-structure-suspension X)) Z) ∘
      ( map-inv-up-suspension Z)) ~ id
  is-section-map-inv-up-suspension Z =
    is-section-map-inv-is-equiv (up-suspension Z)

  is-retraction-map-inv-up-suspension :
    {l : Level} (Z : UU l) →
    ( ( map-inv-up-suspension Z) ∘
      ( ev-suspension ((suspension-structure-suspension X)) Z)) ~ id
  is-retraction-map-inv-up-suspension Z =
    is-retraction-map-inv-is-equiv (up-suspension Z)

  up-suspension-N-susp :
    {l : Level} (Z : UU l) (c : suspension-structure X Z) →
    (map-inv-up-suspension Z c N-susp) ＝ pr1 c
  up-suspension-N-susp Z c =
    pr1 (htpy-eq-suspension-structure ((is-section-map-inv-up-suspension Z) c))

  up-suspension-S-susp :
    {l : Level} (Z : UU l) (c : suspension-structure X Z) →
    (map-inv-up-suspension Z c S-susp) ＝ pr1 (pr2 c)
  up-suspension-S-susp Z c =
    pr1
      ( pr2
        ( htpy-eq-suspension-structure (is-section-map-inv-up-suspension Z c)))

  up-suspension-merid-susp :
    {l : Level} (Z : UU l) (c : suspension-structure X Z) (x : X) →
    ( ( ap (map-inv-up-suspension Z c) (merid-susp x)) ∙
      ( up-suspension-S-susp Z c)) ＝
    ( ( up-suspension-N-susp Z c) ∙ ( pr2 (pr2 c)) x)
  up-suspension-merid-susp Z c =
    pr2
      ( pr2
        ( htpy-eq-suspension-structure (is-section-map-inv-up-suspension Z c)))

  ev-suspension-up-suspension :
    {l : Level} (Z : UU l) (c : suspension-structure X Z) →
    ( ev-suspension
      ( suspension-structure-suspension X)
      ( Z)
      ( map-inv-up-suspension Z c)) ＝ c
  ev-suspension-up-suspension {l} Z c =
    eq-htpy-suspension-structure
      ( ( up-suspension-N-susp Z c) ,
        ( ( up-suspension-S-susp Z c) ,
          ( up-suspension-merid-susp Z c)))
```

### Dependent Suspension Structures

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  (c : suspension-cocone X Y)
  where

  dependent-suspension-cocone : UU (l1 ⊔ l3)
  dependent-suspension-cocone =
    dependent-cocone
      ( const X unit star)
      ( const X unit star)
      ( c)
      ( B)
```

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  (susp-str : suspension-structure X Y)
  (B : Y → UU l3)
  where

  dependent-suspension-structure : UU (l1 ⊔ l3)
  dependent-suspension-structure =
    Σ ( B (N-suspension-structure susp-str))
      ( λ N →
        Σ ( B (S-suspension-structure susp-str))
          ( λ S →
            (x : X) →
            dependent-identification
              ( B)
              ( merid-suspension-structure susp-str x)
              ( N)
              ( S)))

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {B : Y → UU l3}
  {susp-str : suspension-structure X Y}
  (d-susp-str : dependent-suspension-structure susp-str B)
  where

  N-dependent-suspension-structure : B (N-suspension-structure susp-str)
  N-dependent-suspension-structure = pr1 (d-susp-str)

  S-dependent-suspension-structure : B (S-suspension-structure susp-str)
  S-dependent-suspension-structure = (pr1 ∘ pr2) (d-susp-str)

  merid-dependent-suspension-structure :
    (x : X) →
    dependent-identification
      ( B)
      ( merid-suspension-structure susp-str x)
      ( N-dependent-suspension-structure)
      ( S-dependent-suspension-structure)
  merid-dependent-suspension-structure = (pr2 ∘ pr2) (d-susp-str)
```

#### Characterizing equality of dependent suspension structures

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  {susp-str : suspension-structure X Y}
  (d-susp-str0 d-susp-str1 : dependent-suspension-structure susp-str B)
  where

  htpy-dependent-suspension-structure : UU (l1 ⊔ l3)
  htpy-dependent-suspension-structure =
    Σ ( N-dependent-suspension-structure d-susp-str0 ＝
        N-dependent-suspension-structure d-susp-str1)
      ( λ N-htpy →
        Σ ( S-dependent-suspension-structure d-susp-str0 ＝
            S-dependent-suspension-structure d-susp-str1)
          ( λ S-htpy →
            (x : X) →
            coherence-square-identifications
              ( merid-dependent-suspension-structure d-susp-str0 x)
              ( S-htpy)
              ( ap
                ( tr B (merid-suspension-structure susp-str x))
                ( N-htpy))
              ( merid-dependent-suspension-structure d-susp-str1 x)))

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  {susp-str : suspension-structure X Y}
  (d-susp-str0 : dependent-suspension-structure susp-str B)
  where

  extensionality-dependent-suspension-structure :
    ( d-susp-str1 : dependent-suspension-structure susp-str B) →
    ( d-susp-str0 ＝ d-susp-str1) ≃
    ( htpy-dependent-suspension-structure B d-susp-str0 d-susp-str1)
  extensionality-dependent-suspension-structure =
    extensionality-Σ
      ( λ (S , m) (N-htpy) →
        Σ (S-dependent-suspension-structure d-susp-str0 ＝ S)
          ( λ S-htpy →
            (x : X) →
            coherence-square-identifications
              ( merid-dependent-suspension-structure d-susp-str0 x)
              ( S-htpy)
              ( ap (tr B (merid-suspension-structure susp-str x)) N-htpy)
              ( m x)))
      ( refl)
      ( refl , λ x → right-unit)
      ( λ N → id-equiv)
      ( extensionality-Σ
        ( λ m S-htpy →
          (x : X) →
          ( merid-dependent-suspension-structure d-susp-str0 x ∙ S-htpy) ＝
          ( m x))
        ( refl)
        ( λ x → right-unit)
        ( λ S → id-equiv)
        ( λ m →
          equiv-concat-htpy right-unit-htpy m ∘e inv-equiv equiv-eq-htpy))

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  {susp-str : suspension-structure X Y}
  {d-susp-str0 d-susp-str1 : dependent-suspension-structure susp-str B}
  where

  htpy-eq-dependent-suspension-structure :
    (d-susp-str0 ＝ d-susp-str1) →
    htpy-dependent-suspension-structure B d-susp-str0 d-susp-str1
  htpy-eq-dependent-suspension-structure =
    map-equiv
      ( extensionality-dependent-suspension-structure B d-susp-str0 d-susp-str1)

  eq-htpy-dependent-suspension-structure :
    htpy-dependent-suspension-structure B d-susp-str0 d-susp-str1 →
    d-susp-str0 ＝ d-susp-str1
  eq-htpy-dependent-suspension-structure =
    map-inv-equiv
      ( extensionality-dependent-suspension-structure B d-susp-str0 d-susp-str1)

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  {susp-str : suspension-structure X Y}
  (d-susp-str : dependent-suspension-structure susp-str B)
  where

  refl-htpy-dependent-suspension-structure :
    htpy-dependent-suspension-structure B d-susp-str d-susp-str
  pr1 refl-htpy-dependent-suspension-structure = refl
  pr1 (pr2 refl-htpy-dependent-suspension-structure) = refl
  pr2 (pr2 refl-htpy-dependent-suspension-structure) x = right-unit

  is-refl-refl-htpy-dependent-suspension-structure :
    refl-htpy-dependent-suspension-structure ＝
    htpy-eq-dependent-suspension-structure B refl
  is-refl-refl-htpy-dependent-suspension-structure = refl
```

### The dependent universal property of suspensions

```agda
dependent-ev-suspension :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  (susp-str : suspension-structure X Y) (B : Y → UU l3) →
  ((y : Y) → B y) →
  dependent-suspension-structure susp-str B
pr1 (dependent-ev-suspension susp-str B s) =
  s (N-suspension-structure susp-str)
pr1 (pr2 (dependent-ev-suspension susp-str B s)) =
  s (S-suspension-structure susp-str)
pr2 (pr2 (dependent-ev-suspension susp-str B s)) =
  (apd s) ∘ (merid-suspension-structure susp-str)

module _
  (l : Level) {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (susp-str : suspension-structure X Y)
  where

  dependent-universal-property-suspension : UU (l1 ⊔ l2 ⊔ lsuc l)
  dependent-universal-property-suspension =
    (B : Y → UU l) → is-equiv (dependent-ev-suspension susp-str B)
```

### The suspension-loop space adjunction

Here we prove the universal property of the suspension of a pointed type: the
suspension is left adjoint to the loop space. We do this by constructing an
equivalence ((suspension A) →∗ B) ≃ (A →∗ Ω B) and showing this equivalences is
given by λ f → Ω(f) ∘ unit

#### The unit and counit of the adjunction

```agda
module _
  {l1 : Level} (X : Pointed-Type l1)
  where

  shift : (type-Ω (suspension-Pointed-Type X)) → (N-susp ＝ S-susp)
  shift l = l ∙ (merid-susp (point-Pointed-Type X))

  shift∗ :
    Ω (suspension-Pointed-Type X) →∗
    ((N-susp ＝ S-susp) , (merid-susp (point-Pointed-Type X)))
  pr1 shift∗ = shift
  pr2 shift∗ = refl

  unshift : (N-susp ＝ S-susp) → (type-Ω (suspension-Pointed-Type X))
  unshift p = p ∙ inv (merid-susp (point-Pointed-Type X))

  unshift∗ :
    ((N-susp ＝ S-susp) , (merid-susp (point-Pointed-Type X))) →∗
    Ω (suspension-Pointed-Type X)
  pr1 unshift∗ = unshift
  pr2 unshift∗ = right-inv (merid-susp (point-Pointed-Type X))

  is-equiv-shift : is-equiv shift
  is-equiv-shift = is-equiv-concat' N-susp (merid-susp (point-Pointed-Type X))

  pointed-equiv-shift :
    ( Ω (suspension-Pointed-Type X)) ≃∗
    ( (N-susp ＝ S-susp) , merid-susp (point-Pointed-Type X))
  pr1 (pr1 pointed-equiv-shift) = shift
  pr2 (pr1 pointed-equiv-shift) = is-equiv-shift
  pr2 pointed-equiv-shift = preserves-point-pointed-map shift∗

  merid-susp∗ : X →∗ ((N-susp ＝ S-susp) , (merid-susp (point-Pointed-Type X)))
  pr1 merid-susp∗ = merid-susp
  pr2 merid-susp∗ = refl

  unit-susp-loop-adj∗ : X →∗ Ω (suspension-Pointed-Type X)
  unit-susp-loop-adj∗ = unshift∗ ∘∗ merid-susp∗

  unit-susp-loop-adj : type-Pointed-Type X → type-Ω (suspension-Pointed-Type X)
  unit-susp-loop-adj = map-pointed-map unit-susp-loop-adj∗

  counit-susp-loop-adj : (suspension (type-Ω X)) → type-Pointed-Type X
  counit-susp-loop-adj =
    map-inv-is-equiv
      ( up-suspension (type-Ω X) (type-Pointed-Type X))
      ( ( point-Pointed-Type X) ,
        ( point-Pointed-Type X) ,
        ( id))

  counit-susp-loop-adj∗ : ((suspension (type-Ω X)) , N-susp) →∗ X
  pr1 counit-susp-loop-adj∗ = counit-susp-loop-adj
  pr2 counit-susp-loop-adj∗ =
    up-suspension-N-susp
      ( type-Ω X)
      ( type-Pointed-Type X)
      ( ( point-Pointed-Type X) ,
        ( point-Pointed-Type X) ,
        ( id))
```

#### The underlying map of the equivalence

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  map-equiv-susp-loop-adj :
    ((suspension-Pointed-Type X) →∗ Y) →
    (X →∗ Ω Y)
  map-equiv-susp-loop-adj f∗ =
    ((pointed-map-Ω f∗) ∘∗ (unit-susp-loop-adj∗ X))
```

#### The underlying map of the inverse of the equivalence

The following function takes a map `X → Ω Y` and returns a suspension structure
on `Y`.

```agda
module _
  {l1 l2 : Level} (X : UU l1) (Y : Pointed-Type l2)
  where
  suspension-structure-map-into-Ω :
    (X → type-Ω Y) → suspension-structure X (type-Pointed-Type Y)
  pr1 (suspension-structure-map-into-Ω f) = point-Pointed-Type Y
  pr1 (pr2 (suspension-structure-map-into-Ω f)) = point-Pointed-Type Y
  pr2 (pr2 (suspension-structure-map-into-Ω f)) = f
```

The above plus the universal property of suspensions defines the inverse map. We
use the universal property to define the inverse.

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  map-inv-equiv-susp-loop-adj :
    (X →∗ Ω Y) → ((suspension-Pointed-Type X) →∗ Y)
  pr1 (map-inv-equiv-susp-loop-adj f∗) =
    map-inv-up-suspension
      ( type-Pointed-Type X)
      ( type-Pointed-Type Y)
      ( suspension-structure-map-into-Ω
        ( type-Pointed-Type X)
        ( Y)
        ( map-pointed-map f∗))
  pr2 (map-inv-equiv-susp-loop-adj f∗) =
    up-suspension-N-susp
      ( type-Pointed-Type X)
      ( type-Pointed-Type Y)
      ( suspension-structure-map-into-Ω
      ( type-Pointed-Type X)
      ( Y)
      ( map-pointed-map f∗))
```

We now show these maps are inverses of each other.

[To Do]

#### The equivalence between pointed maps out of the suspension of X and pointed maps into the loop space of Y

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  equiv-susp-loop-adj : (suspension-Pointed-Type X →∗ Y) ≃ (X →∗ Ω Y)
  equiv-susp-loop-adj =
    ( left-unit-law-Σ-is-contr
      ( is-contr-total-path (point-Pointed-Type Y))
      ( (point-Pointed-Type Y) , refl)) ∘e
    ( ( inv-equiv
        ( associative-Σ
          ( type-Pointed-Type Y)
          ( λ z → (point-Pointed-Type Y) ＝ z)
          ( λ t →
            Σ ( type-Pointed-Type X → (point-Pointed-Type Y) ＝ (pr1 t))
              ( λ f → f (point-Pointed-Type X) ＝ (pr2 t))))) ∘e
      ( ( equiv-tot (λ y1 → equiv-left-swap-Σ)) ∘e
        ( ( associative-Σ
            ( type-Pointed-Type Y)
            ( λ y1 → type-Pointed-Type X → (point-Pointed-Type Y) ＝ y1)
            ( λ z →
              Σ ( Id (point-Pointed-Type Y) (pr1 z))
                ( λ x → pr2 z (point-Pointed-Type X) ＝ x))) ∘e
          ( ( inv-equiv
              ( right-unit-law-Σ-is-contr
                ( λ ( z : Σ ( type-Pointed-Type Y)
                            ( λ y1 →
                              type-Pointed-Type X →
                              point-Pointed-Type Y ＝ y1)) →
                  is-contr-total-path ((pr2 z) (point-Pointed-Type X))))) ∘e
            ( ( left-unit-law-Σ-is-contr
                ( is-contr-total-path' (point-Pointed-Type Y))
                ( (point-Pointed-Type Y) , refl)) ∘e
              ( ( equiv-right-swap-Σ) ∘e
                ( equiv-Σ-equiv-base
                  ( λ c → (pr1 c) ＝ (point-Pointed-Type Y))
                  ( equiv-up-suspension
                    ( type-Pointed-Type X)
                    ( type-Pointed-Type Y)))))))))
```

#### The equivalence in the suspension-loop space adjunction is pointed

This remains to be shown.

### The suspension of a contractible type is contractible

```agda
is-contr-suspension-is-contr :
  {l : Level} {X : UU l} → is-contr X → is-contr (suspension X)
is-contr-suspension-is-contr {l} {X} is-contr-X =
  is-contr-is-equiv'
    ( unit)
    ( pr1 (pr2 (cocone-pushout (const X unit star) (const X unit star))))
    ( is-equiv-universal-property-pushout
      ( const X unit star)
      ( const X unit star)
      ( cocone-pushout
        ( const X unit star)
        ( const X unit star))
      ( is-equiv-is-contr (const X unit star) is-contr-X is-contr-unit)
      ( up-pushout (const X unit star) (const X unit star)))
    ( is-contr-unit)
```
