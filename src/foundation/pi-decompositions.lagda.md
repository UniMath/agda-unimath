# Π-decompositions of types

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.pi-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Idea

A Π-decomposition of a type `A` consists of a type `X` and a family of types
`Y x` indexed by `x : X` equipped with an equivalence `A ≃ Π X Y`. The type `X`
is called the indexing type of the Π-decomposition, the elements of `Y x` are
called the cotypes of the Π-decomposition, and the equivalence `A ≃ Π X Y` is
the matching correspondence of the Π-decomposition

## Definitions

### Π type

```agda
Π : {l1 l2 : Level} (X : UU l1) (Y : X → UU l2) → UU (l1 ⊔ l2)
Π X Y = (x : X) → Y x
```

### General Π-decompositions

```agda
Π-Decomposition :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Π-Decomposition l2 l3 A =
  Σ ( UU l2)
    ( λ X →
      Σ ( X → UU l3)
        ( λ Y → A ≃ Π X Y))

module _
  {l1 l2 l3 : Level} {A : UU l1} (D : Π-Decomposition l2 l3 A)
  where

  indexing-type-Π-Decomposition : UU l2
  indexing-type-Π-Decomposition = pr1 D

  cotype-Π-Decomposition : indexing-type-Π-Decomposition → UU l3
  cotype-Π-Decomposition = pr1 (pr2 D)

  matching-correspondence-Π-Decomposition :
    A ≃ Π indexing-type-Π-Decomposition cotype-Π-Decomposition
  matching-correspondence-Π-Decomposition = pr2 (pr2 D)

  map-matching-correspondence-Π-Decomposition :
    A → Π indexing-type-Π-Decomposition cotype-Π-Decomposition
  map-matching-correspondence-Π-Decomposition =
    map-equiv matching-correspondence-Π-Decomposition
```

### Fibered Π-decompositions

```agda
fibered-Π-Decomposition :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : UU l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
fibered-Π-Decomposition l2 l3 l4 l5 A =
  Σ ( Π-Decomposition l2 l3 A)
    ( Π-Decomposition l4 l5 ∘ indexing-type-Π-Decomposition)

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : fibered-Π-Decomposition l2 l3 l4 l5 A)
  where

  fst-fibered-Π-Decomposition : Π-Decomposition l2 l3 A
  fst-fibered-Π-Decomposition = pr1 X

  indexing-type-fst-fibered-Π-Decomposition : UU l2
  indexing-type-fst-fibered-Π-Decomposition =
    indexing-type-Π-Decomposition fst-fibered-Π-Decomposition

  cotype-fst-fibered-Π-Decomposition :
    indexing-type-fst-fibered-Π-Decomposition → UU l3
  cotype-fst-fibered-Π-Decomposition =
    cotype-Π-Decomposition fst-fibered-Π-Decomposition

  matching-correspondence-fst-fibered-Π-Decomposition :
    A ≃
    Π ( indexing-type-Π-Decomposition
        ( fst-fibered-Π-Decomposition))
      ( cotype-Π-Decomposition fst-fibered-Π-Decomposition)
  matching-correspondence-fst-fibered-Π-Decomposition =
    matching-correspondence-Π-Decomposition
      ( fst-fibered-Π-Decomposition)

  map-matching-correspondence-fst-fibered-Π-Decomposition :
    A →
    Π ( indexing-type-Π-Decomposition
        ( fst-fibered-Π-Decomposition))
      ( cotype-Π-Decomposition fst-fibered-Π-Decomposition)
  map-matching-correspondence-fst-fibered-Π-Decomposition =
    map-matching-correspondence-Π-Decomposition
      fst-fibered-Π-Decomposition

  snd-fibered-Π-Decomposition :
      Π-Decomposition l4 l5
        ( indexing-type-fst-fibered-Π-Decomposition)
  snd-fibered-Π-Decomposition = pr2 X

  indexing-type-snd-fibered-Π-Decomposition : UU l4
  indexing-type-snd-fibered-Π-Decomposition =
    indexing-type-Π-Decomposition snd-fibered-Π-Decomposition

  cotype-snd-fibered-Π-Decomposition :
    indexing-type-snd-fibered-Π-Decomposition → UU l5
  cotype-snd-fibered-Π-Decomposition =
    cotype-Π-Decomposition snd-fibered-Π-Decomposition

  matching-correspondence-snd-fibered-Π-Decomposition :
    indexing-type-fst-fibered-Π-Decomposition ≃
    Π ( indexing-type-Π-Decomposition
        ( snd-fibered-Π-Decomposition))
      ( cotype-Π-Decomposition snd-fibered-Π-Decomposition)
  matching-correspondence-snd-fibered-Π-Decomposition =
    matching-correspondence-Π-Decomposition
      ( snd-fibered-Π-Decomposition)

  map-matching-correspondence-snd-fibered-Π-Decomposition :
    indexing-type-fst-fibered-Π-Decomposition →
    Π ( indexing-type-Π-Decomposition
        ( snd-fibered-Π-Decomposition))
      ( cotype-Π-Decomposition snd-fibered-Π-Decomposition)
  map-matching-correspondence-snd-fibered-Π-Decomposition =
    map-matching-correspondence-Π-Decomposition
      ( snd-fibered-Π-Decomposition)
```

#### Displayed double Π-decompositions

```agda
displayed-Π-Decomposition :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : UU l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
displayed-Π-Decomposition l2 l3 l4 l5 A =
  ( Σ (Π-Decomposition l2 l3 A)
  ( λ D →
    (u : indexing-type-Π-Decomposition D) →
    Π-Decomposition l4 l5 (cotype-Π-Decomposition D u)))

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : displayed-Π-Decomposition l2 l3 l4 l5 A)
  where

  fst-displayed-Π-Decomposition : Π-Decomposition l2 l3 A
  fst-displayed-Π-Decomposition = pr1 X

  indexing-type-fst-displayed-Π-Decomposition : UU l2
  indexing-type-fst-displayed-Π-Decomposition =
    indexing-type-Π-Decomposition fst-displayed-Π-Decomposition

  cotype-fst-displayed-Π-Decomposition :
    indexing-type-fst-displayed-Π-Decomposition → UU l3
  cotype-fst-displayed-Π-Decomposition =
    cotype-Π-Decomposition fst-displayed-Π-Decomposition

  matching-correspondence-fst-displayed-Π-Decomposition :
    A ≃
    Π ( indexing-type-Π-Decomposition
        fst-displayed-Π-Decomposition)
      ( cotype-Π-Decomposition fst-displayed-Π-Decomposition)
  matching-correspondence-fst-displayed-Π-Decomposition =
    matching-correspondence-Π-Decomposition
      fst-displayed-Π-Decomposition

  map-matching-correspondence-fst-displayed-Π-Decomposition :
    A →
    Π ( indexing-type-Π-Decomposition
        fst-displayed-Π-Decomposition)
      ( cotype-Π-Decomposition fst-displayed-Π-Decomposition)
  map-matching-correspondence-fst-displayed-Π-Decomposition =
    map-matching-correspondence-Π-Decomposition
      fst-displayed-Π-Decomposition

  snd-displayed-Π-Decomposition :
    ( x : indexing-type-fst-displayed-Π-Decomposition) →
    Π-Decomposition l4 l5
      ( cotype-fst-displayed-Π-Decomposition x)
  snd-displayed-Π-Decomposition = pr2 X

  indexing-type-snd-displayed-Π-Decomposition :
    ( x : indexing-type-fst-displayed-Π-Decomposition) →
    UU l4
  indexing-type-snd-displayed-Π-Decomposition x =
    indexing-type-Π-Decomposition
      ( snd-displayed-Π-Decomposition x)

  cotype-snd-displayed-Π-Decomposition :
    ( x : indexing-type-fst-displayed-Π-Decomposition) →
    indexing-type-snd-displayed-Π-Decomposition x →
    UU l5
  cotype-snd-displayed-Π-Decomposition x =
    cotype-Π-Decomposition (snd-displayed-Π-Decomposition x)

  matching-correspondence-snd-displayed-Π-Decomposition :
    ( x : indexing-type-fst-displayed-Π-Decomposition) →
    ( cotype-fst-displayed-Π-Decomposition x ≃
      Π ( indexing-type-snd-displayed-Π-Decomposition x)
        ( cotype-snd-displayed-Π-Decomposition x))
  matching-correspondence-snd-displayed-Π-Decomposition x =
    matching-correspondence-Π-Decomposition
      ( snd-displayed-Π-Decomposition x)

  map-matching-correspondence-snd-displayed-Π-Decomposition :
    ( x : indexing-type-fst-displayed-Π-Decomposition) →
    cotype-fst-displayed-Π-Decomposition x →
    Π ( indexing-type-snd-displayed-Π-Decomposition x)
      ( cotype-snd-displayed-Π-Decomposition x)
  map-matching-correspondence-snd-displayed-Π-Decomposition x =
    map-matching-correspondence-Π-Decomposition
      ( snd-displayed-Π-Decomposition x)
```

## Properties

### Characterization of equality of Π-decompositions

```agda
equiv-Π-Decomposition :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : Π-Decomposition l2 l3 A)
  (Y : Π-Decomposition l4 l5 A) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
equiv-Π-Decomposition X Y =
  Σ ( indexing-type-Π-Decomposition X ≃
      indexing-type-Π-Decomposition Y)
    ( λ e →
      Σ ( (x : indexing-type-Π-Decomposition X) →
          cotype-Π-Decomposition X x ≃
          cotype-Π-Decomposition Y (map-equiv e x))
        ( λ f →
          ( map-equiv-Π (λ z → cotype-Π-Decomposition Y z) e f ∘
            ( map-matching-correspondence-Π-Decomposition X)) ~
          ( map-matching-correspondence-Π-Decomposition Y)))

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : Π-Decomposition l2 l3 A) (Y : Π-Decomposition l4 l5 A)
  (e : equiv-Π-Decomposition X Y)
  where

  equiv-indexing-type-equiv-Π-Decomposition :
    indexing-type-Π-Decomposition X ≃
    indexing-type-Π-Decomposition Y
  equiv-indexing-type-equiv-Π-Decomposition = pr1 e

  map-equiv-indexing-type-equiv-Π-Decomposition :
    indexing-type-Π-Decomposition X →
    indexing-type-Π-Decomposition Y
  map-equiv-indexing-type-equiv-Π-Decomposition =
    map-equiv equiv-indexing-type-equiv-Π-Decomposition

  equiv-cotype-equiv-Π-Decomposition :
    (x : indexing-type-Π-Decomposition X) →
    cotype-Π-Decomposition X x ≃
    cotype-Π-Decomposition Y
      ( map-equiv-indexing-type-equiv-Π-Decomposition x)
  equiv-cotype-equiv-Π-Decomposition = pr1 (pr2 e)

  map-equiv-cotype-equiv-Π-Decomposition :
    (x : indexing-type-Π-Decomposition X) →
    cotype-Π-Decomposition X x →
    cotype-Π-Decomposition Y
      ( map-equiv-indexing-type-equiv-Π-Decomposition x)
  map-equiv-cotype-equiv-Π-Decomposition x =
    map-equiv (equiv-cotype-equiv-Π-Decomposition x)

module _
  {l1 l2 l3 : Level} {A : UU l1} (X : Π-Decomposition l2 l3 A)
  where

  id-equiv-Π-Decomposition : equiv-Π-Decomposition X X
  pr1 id-equiv-Π-Decomposition = id-equiv
  pr1 (pr2 id-equiv-Π-Decomposition) x = id-equiv
  pr2 (pr2 id-equiv-Π-Decomposition) =
    id-map-equiv-Π (λ x → cotype-Π-Decomposition X x) ·r
    map-matching-correspondence-Π-Decomposition X

  is-torsorial-equiv-Π-Decomposition :
    is-torsorial (equiv-Π-Decomposition X)
  is-torsorial-equiv-Π-Decomposition =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (indexing-type-Π-Decomposition X))
      ( pair (indexing-type-Π-Decomposition X) id-equiv)
      ( is-torsorial-Eq-structure
        ( is-torsorial-equiv-fam
          ( cotype-Π-Decomposition X))
        ( pair
          ( cotype-Π-Decomposition X)
          ( id-equiv-fam (cotype-Π-Decomposition X)))
        ( is-torsorial-htpy-equiv
          ( ( equiv-Π
              ( cotype-Π-Decomposition X)
              ( id-equiv)
              ( λ _ → id-equiv)) ∘e
            ( matching-correspondence-Π-Decomposition X))))

  equiv-eq-Π-Decomposition :
    (Y : Π-Decomposition l2 l3 A) →
    (X ＝ Y) → equiv-Π-Decomposition X Y
  equiv-eq-Π-Decomposition .X refl = id-equiv-Π-Decomposition

  is-equiv-equiv-eq-Π-Decomposition :
    (Y : Π-Decomposition l2 l3 A) →
    is-equiv (equiv-eq-Π-Decomposition Y)
  is-equiv-equiv-eq-Π-Decomposition =
    fundamental-theorem-id
      is-torsorial-equiv-Π-Decomposition
      equiv-eq-Π-Decomposition

  extensionality-Π-Decomposition :
    (Y : Π-Decomposition l2 l3 A) →
    (X ＝ Y) ≃ equiv-Π-Decomposition X Y
  pr1 (extensionality-Π-Decomposition Y) =
    equiv-eq-Π-Decomposition Y
  pr2 (extensionality-Π-Decomposition Y) =
    is-equiv-equiv-eq-Π-Decomposition Y

  eq-equiv-Π-Decomposition :
    (Y : Π-Decomposition l2 l3 A) →
    equiv-Π-Decomposition X Y → (X ＝ Y)
  eq-equiv-Π-Decomposition Y =
    map-inv-equiv (extensionality-Π-Decomposition Y)
```

### Invariance of Π-decompositions under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  equiv-tr-Π-Decomposition :
    {l3 l4 : Level} →
    Π-Decomposition l3 l4 A ≃ Π-Decomposition l3 l4 B
  equiv-tr-Π-Decomposition =
    equiv-tot
      ( λ X →
        equiv-tot
          ( λ Y → equiv-precomp-equiv (inv-equiv e) (Π X Y)))

  map-equiv-tr-Π-Decomposition :
    {l3 l4 : Level} →
    Π-Decomposition l3 l4 A → Π-Decomposition l3 l4 B
  map-equiv-tr-Π-Decomposition =
    map-equiv equiv-tr-Π-Decomposition
```

### Iterated Π-decompositions

#### Characterization of identity type for fibered double Π-decompositions

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (X : fibered-Π-Decomposition l2 l3 l4 l5 A)
  (Y : fibered-Π-Decomposition l6 l7 l8 l9 A)
  where

  equiv-fst-fibered-Π-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
  equiv-fst-fibered-Π-Decomposition =
    equiv-Π-Decomposition
    ( fst-fibered-Π-Decomposition X)
    ( fst-fibered-Π-Decomposition Y)

  equiv-snd-fibered-Π-Decomposition :
    (e : equiv-fst-fibered-Π-Decomposition) →
    UU (l4 ⊔ l5 ⊔ l6 ⊔ l8 ⊔ l9)
  equiv-snd-fibered-Π-Decomposition e =
    equiv-Π-Decomposition
      ( map-equiv-tr-Π-Decomposition
        ( equiv-indexing-type-equiv-Π-Decomposition
          ( fst-fibered-Π-Decomposition X)
          ( fst-fibered-Π-Decomposition Y)
          ( e))
        ( snd-fibered-Π-Decomposition X))
      ( snd-fibered-Π-Decomposition Y)

  equiv-fibered-Π-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-fibered-Π-Decomposition =
    Σ ( equiv-fst-fibered-Π-Decomposition)
      ( equiv-snd-fibered-Π-Decomposition)

  fst-equiv-fibered-Π-Decomposition :
    (e : equiv-fibered-Π-Decomposition) →
    equiv-fst-fibered-Π-Decomposition
  fst-equiv-fibered-Π-Decomposition = pr1

  snd-equiv-fibered-Π-Decomposition :
    (e : equiv-fibered-Π-Decomposition) →
    equiv-snd-fibered-Π-Decomposition
      (fst-equiv-fibered-Π-Decomposition e)
  snd-equiv-fibered-Π-Decomposition = pr2

module _
  { l1 l2 l3 l4 l5 : Level} {A : UU l1}
  ( D : fibered-Π-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = fst-fibered-Π-Decomposition D
    Y = snd-fibered-Π-Decomposition D

  is-torsorial-equiv-fibered-Π-Decomposition :
    is-torsorial (equiv-fibered-Π-Decomposition D)
  is-torsorial-equiv-fibered-Π-Decomposition =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv-Π-Decomposition X)
      ( X , id-equiv-Π-Decomposition X)
      ( is-torsorial-Eq-structure
        ( is-torsorial-equiv (indexing-type-Π-Decomposition Y))
        ( pair (indexing-type-Π-Decomposition Y) id-equiv)
        ( is-torsorial-Eq-structure
          ( is-torsorial-equiv-fam
            ( cotype-Π-Decomposition Y))
          ( pair
            ( cotype-Π-Decomposition Y)
            ( id-equiv-fam
              ( cotype-Π-Decomposition Y)))
            ( is-torsorial-htpy-equiv
              ( ( equiv-Π
                  ( cotype-Π-Decomposition Y)
                  ( id-equiv)
                  ( λ _ → id-equiv)) ∘e
                ( matching-correspondence-Π-Decomposition Y)))))

  id-equiv-fibered-Π-Decomposition :
    equiv-fibered-Π-Decomposition D D
  pr1 id-equiv-fibered-Π-Decomposition =
    id-equiv-Π-Decomposition X
  pr1 (pr2 id-equiv-fibered-Π-Decomposition) = id-equiv
  pr1 (pr2 (pr2 id-equiv-fibered-Π-Decomposition)) x = id-equiv
  pr2 (pr2 (pr2 id-equiv-fibered-Π-Decomposition)) =
    id-map-equiv-Π (cotype-snd-fibered-Π-Decomposition D) ·r
    map-matching-correspondence-snd-fibered-Π-Decomposition D

  equiv-eq-fibered-Π-Decomposition :
    (D' : fibered-Π-Decomposition l2 l3 l4 l5 A) →
    (D ＝ D') → equiv-fibered-Π-Decomposition D D'
  equiv-eq-fibered-Π-Decomposition .D refl =
    id-equiv-fibered-Π-Decomposition

  is-equiv-equiv-eq-fibered-Π-Decomposition :
    (D' : fibered-Π-Decomposition l2 l3 l4 l5 A) →
    is-equiv (equiv-eq-fibered-Π-Decomposition D')
  is-equiv-equiv-eq-fibered-Π-Decomposition =
    fundamental-theorem-id
      is-torsorial-equiv-fibered-Π-Decomposition
      equiv-eq-fibered-Π-Decomposition

  extensionality-fibered-Π-Decomposition :
    (D' : fibered-Π-Decomposition l2 l3 l4 l5 A) →
    (D ＝ D') ≃ equiv-fibered-Π-Decomposition D D'
  pr1 (extensionality-fibered-Π-Decomposition D') =
    equiv-eq-fibered-Π-Decomposition D'
  pr2 (extensionality-fibered-Π-Decomposition D') =
    is-equiv-equiv-eq-fibered-Π-Decomposition D'

  eq-equiv-fibered-Π-Decomposition :
    (D' : fibered-Π-Decomposition l2 l3 l4 l5 A) →
    (equiv-fibered-Π-Decomposition D D') → (D ＝ D')
  eq-equiv-fibered-Π-Decomposition D' =
    map-inv-equiv (extensionality-fibered-Π-Decomposition D')
```

#### Characterization of identity type for displayed double Π-decompositions

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (X : displayed-Π-Decomposition l2 l3 l4 l5 A)
  (Y : displayed-Π-Decomposition l6 l7 l8 l9 A)
  where

  equiv-fst-displayed-Π-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
  equiv-fst-displayed-Π-Decomposition =
    equiv-Π-Decomposition
    ( fst-displayed-Π-Decomposition X)
    ( fst-displayed-Π-Decomposition Y)

  equiv-snd-displayed-Π-Decomposition :
    (e : equiv-fst-displayed-Π-Decomposition) →
    UU (l2 ⊔ l4 ⊔ l5 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-snd-displayed-Π-Decomposition e =
    ( x : indexing-type-fst-displayed-Π-Decomposition X) →
    equiv-Π-Decomposition
      ( map-equiv-tr-Π-Decomposition
        ( equiv-cotype-equiv-Π-Decomposition
          ( fst-displayed-Π-Decomposition X)
          ( fst-displayed-Π-Decomposition Y)
          ( e)
          ( x))
        ( snd-displayed-Π-Decomposition X x))
      ( snd-displayed-Π-Decomposition Y
        ( map-equiv-indexing-type-equiv-Π-Decomposition
          ( fst-displayed-Π-Decomposition X)
          ( fst-displayed-Π-Decomposition Y)
          ( e)
          ( x)))

  equiv-displayed-Π-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-displayed-Π-Decomposition =
    Σ ( equiv-fst-displayed-Π-Decomposition)
      ( equiv-snd-displayed-Π-Decomposition)

  fst-equiv-displayed-Π-Decomposition :
    (e : equiv-displayed-Π-Decomposition) →
    equiv-fst-displayed-Π-Decomposition
  fst-equiv-displayed-Π-Decomposition = pr1

  snd-equiv-displayed-Π-Decomposition :
    (e : equiv-displayed-Π-Decomposition) →
    equiv-snd-displayed-Π-Decomposition
      ( fst-equiv-displayed-Π-Decomposition e)
  snd-equiv-displayed-Π-Decomposition = pr2

module _
  { l1 l2 l3 l4 l5 : Level} {A : UU l1}
  ( disp-D : displayed-Π-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = fst-displayed-Π-Decomposition disp-D
    f-Y = snd-displayed-Π-Decomposition disp-D

  is-torsorial-equiv-displayed-Π-Decomposition :
    is-torsorial (equiv-displayed-Π-Decomposition disp-D)
  is-torsorial-equiv-displayed-Π-Decomposition =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv-Π-Decomposition X)
      ( pair X (id-equiv-Π-Decomposition X))
      ( is-contr-equiv
        ( Π-total-fam (λ x → _))
        ( inv-distributive-Π-Σ)
        ( is-contr-Π
          ( λ x → is-torsorial-equiv-Π-Decomposition (f-Y x))))

  id-equiv-displayed-Π-Decomposition :
    equiv-displayed-Π-Decomposition disp-D disp-D
  pr1 id-equiv-displayed-Π-Decomposition =
    id-equiv-Π-Decomposition X
  pr1 (pr2 id-equiv-displayed-Π-Decomposition x) = id-equiv
  pr1 (pr2 (pr2 id-equiv-displayed-Π-Decomposition x)) y = id-equiv
  pr2 (pr2 (pr2 id-equiv-displayed-Π-Decomposition x)) =
    id-map-equiv-Π
      ( cotype-snd-displayed-Π-Decomposition disp-D x) ·r
    map-matching-correspondence-snd-displayed-Π-Decomposition disp-D x

  equiv-eq-displayed-Π-Decomposition :
    (disp-D' : displayed-Π-Decomposition l2 l3 l4 l5 A) →
    (disp-D ＝ disp-D') → equiv-displayed-Π-Decomposition disp-D disp-D'
  equiv-eq-displayed-Π-Decomposition .disp-D refl =
    id-equiv-displayed-Π-Decomposition

  is-equiv-equiv-eq-displayed-Π-Decomposition :
    (disp-D' : displayed-Π-Decomposition l2 l3 l4 l5 A) →
    is-equiv (equiv-eq-displayed-Π-Decomposition disp-D')
  is-equiv-equiv-eq-displayed-Π-Decomposition =
    fundamental-theorem-id
      is-torsorial-equiv-displayed-Π-Decomposition
      equiv-eq-displayed-Π-Decomposition

  extensionality-displayed-Π-Decomposition :
    (disp-D' : displayed-Π-Decomposition l2 l3 l4 l5 A) →
    (disp-D ＝ disp-D') ≃ equiv-displayed-Π-Decomposition disp-D disp-D'
  pr1 (extensionality-displayed-Π-Decomposition D) =
    equiv-eq-displayed-Π-Decomposition D
  pr2 (extensionality-displayed-Π-Decomposition D) =
    is-equiv-equiv-eq-displayed-Π-Decomposition D

  eq-equiv-displayed-Π-Decomposition :
    (disp-D' : displayed-Π-Decomposition l2 l3 l4 l5 A) →
    (equiv-displayed-Π-Decomposition disp-D disp-D') →
    (disp-D ＝ disp-D')
  eq-equiv-displayed-Π-Decomposition D =
    map-inv-equiv
      (extensionality-displayed-Π-Decomposition D)
```
