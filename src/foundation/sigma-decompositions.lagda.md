#  Σ-decompositions of types

```agda
module foundation.sigma-decompositions where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equational-reasoning
open import foundation.equivalences
open import foundation.equivalence-extensionality
open import foundation.functions
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels
```

## Idea

A Σ-decomposition of a type `A` consists of a type `X` and a family of inhabited types `Y x` indexed by `x : A` equipped with an equivalence `A ≃ Σ X Y`. The type `X` is called the indexing type of the Σ-decomposition, the elements of `Y x` are called the cotypes of the Σ-decomposition, and the equivalence `A ≃ Σ X Y` is the matching correspondence of the Σ-decomposition

Note that types may have many Σ-decomposition. The type of Σ-decompositions of the unit type, for instance, is equivalent to the type of all pointed connected types. Alternatively, we may think of the type of Σ-decompositions of the unit type as the type of higher groupoid structures on a point, i.e., the type of higher group structures. 

We may restrict to Σ-decompositions where the indexing type is in a given subuniverse, such as the subuniverse of sets or the subuniverse of finite sets.

The type of set-indexed Σ-decompositions of a type `A` is equivalent to the type of equivalence relations on `A`.

## Definitions

### General Σ-decompositions

```agda
Σ-Decomposition :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Σ-Decomposition l2 l3 A =
  Σ ( UU l2)
    ( λ X →
      Σ ( Fam-Inhabited-Types l3 X)
        ( λ Y → A ≃ total-Fam-Inhabited-Types Y))

module _
  {l1 l2 l3 : Level} {A : UU l1} (D : Σ-Decomposition l2 l3 A)
  where

  indexing-type-Σ-Decomposition : UU l2
  indexing-type-Σ-Decomposition = pr1 D

  inhabited-cotype-Σ-Decomposition :
    Fam-Inhabited-Types l3 indexing-type-Σ-Decomposition
  inhabited-cotype-Σ-Decomposition = pr1 (pr2 D)

  cotype-Σ-Decomposition : indexing-type-Σ-Decomposition → UU l3
  cotype-Σ-Decomposition =
    type-Fam-Inhabited-Types inhabited-cotype-Σ-Decomposition

  is-inhabited-cotype-Σ-Decomposition :
    (x : indexing-type-Σ-Decomposition) →
    is-inhabited (cotype-Σ-Decomposition x)
  is-inhabited-cotype-Σ-Decomposition x =
    is-inhabited-type-Inhabited-Type (inhabited-cotype-Σ-Decomposition x)

  matching-correspondence-Σ-Decomposition :
    A ≃ Σ indexing-type-Σ-Decomposition cotype-Σ-Decomposition
  matching-correspondence-Σ-Decomposition = pr2 (pr2 D)

  map-matching-correspondence-Σ-Decomposition :
    A → Σ indexing-type-Σ-Decomposition cotype-Σ-Decomposition
  map-matching-correspondence-Σ-Decomposition =
    map-equiv matching-correspondence-Σ-Decomposition
```

### Set-indexed Σ-decompositions

```agda
Set-Indexed-Σ-Decomposition :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Set-Indexed-Σ-Decomposition l2 l3 A =
  Σ ( Set l2)
    ( λ X →
      Σ ( Fam-Inhabited-Types l3 (type-Set X))
        ( λ Y → A ≃ total-Fam-Inhabited-Types Y))

module _
  {l1 l2 l3 : Level} {A : UU l1} (D : Set-Indexed-Σ-Decomposition l2 l3 A)
  where

  indexing-set-Set-Indexed-Σ-Decomposition : Set l2
  indexing-set-Set-Indexed-Σ-Decomposition = pr1 D

  indexing-type-Set-Indexed-Σ-Decomposition : UU l2
  indexing-type-Set-Indexed-Σ-Decomposition =
    type-Set indexing-set-Set-Indexed-Σ-Decomposition

  inhabited-cotype-Set-Indexed-Σ-Decomposition :
    indexing-type-Set-Indexed-Σ-Decomposition → Inhabited-Type l3
  inhabited-cotype-Set-Indexed-Σ-Decomposition = pr1 (pr2 D)

  cotype-Set-Indexed-Σ-Decomposition :
    indexing-type-Set-Indexed-Σ-Decomposition → UU l3
  cotype-Set-Indexed-Σ-Decomposition x =
    type-Inhabited-Type (inhabited-cotype-Set-Indexed-Σ-Decomposition x)

  is-inhabited-cotype-Set-Indexed-Σ-Decomposition :
    (x : indexing-type-Set-Indexed-Σ-Decomposition) →
    is-inhabited (cotype-Set-Indexed-Σ-Decomposition x)
  is-inhabited-cotype-Set-Indexed-Σ-Decomposition x =
    is-inhabited-type-Inhabited-Type
      ( inhabited-cotype-Set-Indexed-Σ-Decomposition x)

  matching-correspondence-Set-Indexed-Σ-Decomposition :
    A ≃
    Σ indexing-type-Set-Indexed-Σ-Decomposition
      cotype-Set-Indexed-Σ-Decomposition
  matching-correspondence-Set-Indexed-Σ-Decomposition = pr2 (pr2 D)

  map-matching-correspondence-Set-Indexed-Σ-Decomposition :
    A →
    Σ indexing-type-Set-Indexed-Σ-Decomposition
      cotype-Set-Indexed-Σ-Decomposition
  map-matching-correspondence-Set-Indexed-Σ-Decomposition =
    map-equiv matching-correspondence-Set-Indexed-Σ-Decomposition

  index-Set-Indexed-Σ-Decomposition :
    A → indexing-type-Set-Indexed-Σ-Decomposition
  index-Set-Indexed-Σ-Decomposition a =
    pr1 (map-matching-correspondence-Set-Indexed-Σ-Decomposition a)
```

## Properties

### Characterization of equality of Σ-Decompositions

```agda
equiv-Σ-Decomposition :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : Σ-Decomposition l2 l3 A) (Y : Σ-Decomposition l4 l5 A) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
equiv-Σ-Decomposition X Y =
  Σ ( indexing-type-Σ-Decomposition X ≃ indexing-type-Σ-Decomposition Y)
    ( λ e →
      Σ ( (x : indexing-type-Σ-Decomposition X) →
          cotype-Σ-Decomposition X x ≃ cotype-Σ-Decomposition Y (map-equiv e x))
        ( λ f →
          ( ( map-equiv (equiv-Σ (cotype-Σ-Decomposition Y) e f)) ∘
            ( map-matching-correspondence-Σ-Decomposition X)) ~
          ( map-matching-correspondence-Σ-Decomposition Y)))

module _
  {l1 l2 l3 : Level} {A : UU l1} (X : Σ-Decomposition l2 l3 A)
  where

  id-equiv-Σ-Decomposition : equiv-Σ-Decomposition X X
  pr1 id-equiv-Σ-Decomposition = id-equiv
  pr1 (pr2 id-equiv-Σ-Decomposition) x = id-equiv
  pr2 (pr2 id-equiv-Σ-Decomposition) = refl-htpy

  is-contr-total-equiv-Σ-Decomposition :
    is-contr (Σ (Σ-Decomposition l2 l3 A) (equiv-Σ-Decomposition X))
  is-contr-total-equiv-Σ-Decomposition =
    is-contr-total-Eq-structure
      ( λ U Vf e →
        Σ ( (x : indexing-type-Σ-Decomposition X) →
            cotype-Σ-Decomposition X x ≃
            type-Inhabited-Type (pr1 Vf (map-equiv e x)))
          ( λ f →
            ( ( map-equiv
                ( equiv-Σ (λ u → type-Inhabited-Type (pr1 Vf u)) e f)) ∘
              ( map-matching-correspondence-Σ-Decomposition X)) ~
            ( map-equiv (pr2 Vf))))
      ( is-contr-total-equiv (indexing-type-Σ-Decomposition X))
      ( pair (indexing-type-Σ-Decomposition X) id-equiv)
      ( is-contr-total-Eq-structure
        ( λ V g f →
          ( ( map-equiv
              ( equiv-Σ (λ y → type-Inhabited-Type (V y)) id-equiv f)) ∘
            ( map-matching-correspondence-Σ-Decomposition X)) ~
          ( map-equiv g))
        ( is-contr-total-equiv-Fam-Inhabited-Types
          ( inhabited-cotype-Σ-Decomposition X))
        ( pair
          ( inhabited-cotype-Σ-Decomposition X)
          ( id-equiv-Fam-Inhabited-Types (inhabited-cotype-Σ-Decomposition X)))
        ( is-contr-total-htpy-equiv
          ( matching-correspondence-Σ-Decomposition X)))

  equiv-eq-Σ-Decomposition :
    (Y : Σ-Decomposition l2 l3 A) → (X ＝ Y) → equiv-Σ-Decomposition X Y
  equiv-eq-Σ-Decomposition .X refl = id-equiv-Σ-Decomposition

  is-equiv-equiv-eq-Σ-Decomposition :
    (Y : Σ-Decomposition l2 l3 A) → is-equiv (equiv-eq-Σ-Decomposition Y)
  is-equiv-equiv-eq-Σ-Decomposition =
    fundamental-theorem-id
      is-contr-total-equiv-Σ-Decomposition
      equiv-eq-Σ-Decomposition

  extensionality-Σ-Decomposition :
    (Y : Σ-Decomposition l2 l3 A) → (X ＝ Y) ≃ equiv-Σ-Decomposition X Y
  pr1 (extensionality-Σ-Decomposition Y) = equiv-eq-Σ-Decomposition Y
  pr2 (extensionality-Σ-Decomposition Y) = is-equiv-equiv-eq-Σ-Decomposition Y

  eq-equiv-Σ-Decomposition :
    (Y : Σ-Decomposition l2 l3 A) → equiv-Σ-Decomposition X Y → (X ＝ Y)
  eq-equiv-Σ-Decomposition Y =
    map-inv-equiv (extensionality-Σ-Decomposition Y)
```

### Characterization of equality of set-indexed Σ-Decompositions

```agda
equiv-Set-Indexed-Σ-Decomposition :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : Set-Indexed-Σ-Decomposition l2 l3 A)
  (Y : Set-Indexed-Σ-Decomposition l4 l5 A) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
equiv-Set-Indexed-Σ-Decomposition X Y =
  Σ ( indexing-type-Set-Indexed-Σ-Decomposition X ≃
      indexing-type-Set-Indexed-Σ-Decomposition Y)
    ( λ e →
      Σ ( (x : indexing-type-Set-Indexed-Σ-Decomposition X) →
          cotype-Set-Indexed-Σ-Decomposition X x ≃
          cotype-Set-Indexed-Σ-Decomposition Y (map-equiv e x))
        ( λ f →
          ( ( map-equiv (equiv-Σ (cotype-Set-Indexed-Σ-Decomposition Y) e f)) ∘
            ( map-matching-correspondence-Set-Indexed-Σ-Decomposition X)) ~
          ( map-matching-correspondence-Set-Indexed-Σ-Decomposition Y)))

module _
  {l1 l2 l3 : Level} {A : UU l1} (X : Set-Indexed-Σ-Decomposition l2 l3 A)
  where

  id-equiv-Set-Indexed-Σ-Decomposition : equiv-Set-Indexed-Σ-Decomposition X X
  pr1 id-equiv-Set-Indexed-Σ-Decomposition = id-equiv
  pr1 (pr2 id-equiv-Set-Indexed-Σ-Decomposition) x = id-equiv
  pr2 (pr2 id-equiv-Set-Indexed-Σ-Decomposition) = refl-htpy

  is-contr-total-equiv-Set-Indexed-Σ-Decomposition :
    is-contr (Σ (Set-Indexed-Σ-Decomposition l2 l3 A) (equiv-Set-Indexed-Σ-Decomposition X))
  is-contr-total-equiv-Set-Indexed-Σ-Decomposition =
    is-contr-total-Eq-structure
      ( λ U Vf e →
        Σ ( (x : indexing-type-Set-Indexed-Σ-Decomposition X) →
            cotype-Set-Indexed-Σ-Decomposition X x ≃
            type-Inhabited-Type (pr1 Vf (map-equiv e x)))
          ( λ f →
            ( ( map-equiv
                ( equiv-Σ (λ u → type-Inhabited-Type (pr1 Vf u)) e f)) ∘
              ( map-matching-correspondence-Set-Indexed-Σ-Decomposition X)) ~
            ( map-equiv (pr2 Vf))))
      ( is-contr-total-equiv-Set (indexing-set-Set-Indexed-Σ-Decomposition X))
      ( pair (indexing-set-Set-Indexed-Σ-Decomposition X) id-equiv)
      ( is-contr-total-Eq-structure
        ( λ V g f →
          ( ( map-equiv
              ( equiv-Σ (λ y → type-Inhabited-Type (V y)) id-equiv f)) ∘
            ( map-matching-correspondence-Set-Indexed-Σ-Decomposition X)) ~
          ( map-equiv g))
        ( is-contr-total-equiv-Fam-Inhabited-Types
          ( inhabited-cotype-Set-Indexed-Σ-Decomposition X))
        ( pair
          ( inhabited-cotype-Set-Indexed-Σ-Decomposition X)
          ( id-equiv-Fam-Inhabited-Types
            ( inhabited-cotype-Set-Indexed-Σ-Decomposition X)))
        ( is-contr-total-htpy-equiv
          ( matching-correspondence-Set-Indexed-Σ-Decomposition X)))

  equiv-eq-Set-Indexed-Σ-Decomposition :
    (Y : Set-Indexed-Σ-Decomposition l2 l3 A) →
    (X ＝ Y) → equiv-Set-Indexed-Σ-Decomposition X Y
  equiv-eq-Set-Indexed-Σ-Decomposition .X refl =
    id-equiv-Set-Indexed-Σ-Decomposition

  is-equiv-equiv-eq-Set-Indexed-Σ-Decomposition :
    (Y : Set-Indexed-Σ-Decomposition l2 l3 A) →
    is-equiv (equiv-eq-Set-Indexed-Σ-Decomposition Y)
  is-equiv-equiv-eq-Set-Indexed-Σ-Decomposition =
    fundamental-theorem-id
      is-contr-total-equiv-Set-Indexed-Σ-Decomposition
      equiv-eq-Set-Indexed-Σ-Decomposition

  extensionality-Set-Indexed-Σ-Decomposition :
    (Y : Set-Indexed-Σ-Decomposition l2 l3 A) →
    (X ＝ Y) ≃ equiv-Set-Indexed-Σ-Decomposition X Y
  pr1 (extensionality-Set-Indexed-Σ-Decomposition Y) =
    equiv-eq-Set-Indexed-Σ-Decomposition Y
  pr2 (extensionality-Set-Indexed-Σ-Decomposition Y) =
    is-equiv-equiv-eq-Set-Indexed-Σ-Decomposition Y

  eq-equiv-Set-Indexed-Σ-Decomposition :
    (Y : Set-Indexed-Σ-Decomposition l2 l3 A) →
    equiv-Set-Indexed-Σ-Decomposition X Y → (X ＝ Y)
  eq-equiv-Set-Indexed-Σ-Decomposition Y =
    map-inv-equiv (extensionality-Set-Indexed-Σ-Decomposition Y)
```

### Iterated Σ-decompositions

#### Version 1

```agda
fibered-double-Σ-decomposition :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : UU l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
fibered-double-Σ-decomposition l2 l3 l4 l5 A =
  ( Σ (Σ-Decomposition l2 l3 A)
  (λ D → Σ-Decomposition l4 l5 (indexing-type-Σ-Decomposition D)))

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : fibered-double-Σ-decomposition l2 l3 l4 l5 A)
  where

  fst-fibered-double-Σ-decomposition : Σ-Decomposition l2 l3 A
  fst-fibered-double-Σ-decomposition = pr1 X

  indexing-type-fst-fibered-double-Σ-decomposition : UU l2
  indexing-type-fst-fibered-double-Σ-decomposition =
    indexing-type-Σ-Decomposition fst-fibered-double-Σ-decomposition

  cotype-fst-fibered-double-Σ-decomposition :
    indexing-type-fst-fibered-double-Σ-decomposition →
    UU l3
  cotype-fst-fibered-double-Σ-decomposition =
    cotype-Σ-Decomposition fst-fibered-double-Σ-decomposition

  map-matching-correspondence-fst-fibered-double-Σ-Decomposition :
    A →
    Σ (indexing-type-Σ-Decomposition fst-fibered-double-Σ-decomposition)
      (cotype-Σ-Decomposition fst-fibered-double-Σ-decomposition)
  map-matching-correspondence-fst-fibered-double-Σ-Decomposition  =
    map-matching-correspondence-Σ-Decomposition fst-fibered-double-Σ-decomposition

  snd-fibered-double-Σ-decomposition :
      Σ-Decomposition l4 l5 indexing-type-fst-fibered-double-Σ-decomposition 
  snd-fibered-double-Σ-decomposition = pr2 X

  indexing-type-snd-fibered-double-Σ-decomposition : UU l4
  indexing-type-snd-fibered-double-Σ-decomposition =
    indexing-type-Σ-Decomposition snd-fibered-double-Σ-decomposition

  cotype-snd-fibered-double-Σ-decomposition :
    indexing-type-snd-fibered-double-Σ-decomposition →
    UU l5
  cotype-snd-fibered-double-Σ-decomposition =
   cotype-Σ-Decomposition snd-fibered-double-Σ-decomposition

  map-matching-correspondence-snd-fibered-double-Σ-Decomposition :
    indexing-type-fst-fibered-double-Σ-decomposition →
    Σ (indexing-type-Σ-Decomposition snd-fibered-double-Σ-decomposition)
      (cotype-Σ-Decomposition snd-fibered-double-Σ-decomposition)
  map-matching-correspondence-snd-fibered-double-Σ-Decomposition =
    map-matching-correspondence-Σ-Decomposition snd-fibered-double-Σ-decomposition
```

#### Characterization of identity type for version 1

```agda
module _
  {l1 : Level} {l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (X : fibered-double-Σ-decomposition l2 l3 l4 l5 A)
  (Y : fibered-double-Σ-decomposition l6 l7 l8 l9 A)
  where

  type-equiv-fst-fibered-double-Σ-decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
  type-equiv-fst-fibered-double-Σ-decomposition =
    equiv-Σ-Decomposition
    (fst-fibered-double-Σ-decomposition X)
    (fst-fibered-double-Σ-decomposition Y)

  type-equiv-snd-fibered-double-Σ-decomposition :
    (e : type-equiv-fst-fibered-double-Σ-decomposition) →
    UU (l2 ⊔ l4 ⊔ l5 ⊔ l8 ⊔ l9)
  type-equiv-snd-fibered-double-Σ-decomposition e =
     Σ ( indexing-type-snd-fibered-double-Σ-decomposition X ≃
         indexing-type-snd-fibered-double-Σ-decomposition Y)
        λ f →
          Σ ( (u : indexing-type-snd-fibered-double-Σ-decomposition X) →
              cotype-snd-fibered-double-Σ-decomposition X u ≃
              cotype-snd-fibered-double-Σ-decomposition Y ((map-equiv f) u))
            ( λ g →
              ( map-equiv (equiv-Σ (cotype-snd-fibered-double-Σ-decomposition Y) f g) ∘
                ( map-matching-correspondence-snd-fibered-double-Σ-Decomposition X))
              ~
              ( ( map-matching-correspondence-snd-fibered-double-Σ-Decomposition Y) ∘
                map-equiv (pr1 e)))

  equiv-fibered-double-Σ-decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-fibered-double-Σ-decomposition =
    Σ ( type-equiv-fst-fibered-double-Σ-decomposition)
      ( type-equiv-snd-fibered-double-Σ-decomposition)

  fst-equiv-fibered-double-Σ-decomposition :
    (e : equiv-fibered-double-Σ-decomposition) →
    type-equiv-fst-fibered-double-Σ-decomposition
  fst-equiv-fibered-double-Σ-decomposition = pr1

  snd-equiv-fibered-double-Σ-decomposition :
    (e : equiv-fibered-double-Σ-decomposition) →
    type-equiv-snd-fibered-double-Σ-decomposition
      (fst-equiv-fibered-double-Σ-decomposition e)
  snd-equiv-fibered-double-Σ-decomposition = pr2

module _
  { l1 l2 l3 l4 l5 : Level}  {A : UU l1}
  ( (X , Y) : fibered-double-Σ-decomposition l2 l3 l4 l5 A)
  where

  is-contr-total-equiv-fibered-double-Σ-Decomposition :
    is-contr ( Σ ( fibered-double-Σ-decomposition l2 l3 l4 l5 A )
          (equiv-fibered-double-Σ-decomposition (pair X Y)))
  is-contr-total-equiv-fibered-double-Σ-Decomposition =
    is-contr-total-Eq-structure
      ( λ X' Y' e → type-equiv-snd-fibered-double-Σ-decomposition
        (pair X Y) (pair X' Y') e)
      ( is-contr-total-equiv-Σ-Decomposition X)
      ( pair X (id-equiv-Σ-Decomposition X))
      ( is-contr-total-Eq-structure
        ( λ U Vs e →
          ( Σ ( (u : indexing-type-Σ-Decomposition Y) →
               cotype-Σ-Decomposition Y u ≃
               type-Inhabited-Type (pr1 Vs (map-equiv e u)))
             ( λ f →
                ( ( map-equiv (equiv-Σ (λ u → type-Inhabited-Type (pr1 Vs u)) e f) ∘
                  ( map-matching-correspondence-Σ-Decomposition Y)) ~
                  (map-equiv (pr2 Vs))
                  ))))
        ( is-contr-total-equiv (indexing-type-Σ-Decomposition Y))
        ( pair (indexing-type-Σ-Decomposition Y) id-equiv )
        ( is-contr-total-Eq-structure
           ( λ V f g →
             ( map-equiv
               ( equiv-Σ ( λ u → type-Inhabited-Type (V  u)) id-equiv g)
              ∘  map-equiv (matching-correspondence-Σ-Decomposition Y)) ~
              ( pr1 f)
             )
           ( is-contr-total-equiv-Fam-Inhabited-Types
             ( inhabited-cotype-Σ-Decomposition Y))
           ( pair
             ( inhabited-cotype-Σ-Decomposition Y)
             ( id-equiv-Fam-Inhabited-Types (inhabited-cotype-Σ-Decomposition Y)))
             ( is-contr-total-htpy-equiv (matching-correspondence-Σ-Decomposition Y) )))

  id-equiv-fibered-double-Σ-Decomposition :
    equiv-fibered-double-Σ-decomposition (pair X Y) (pair X Y)
  pr1 id-equiv-fibered-double-Σ-Decomposition = id-equiv-Σ-Decomposition X
  pr1 (pr2 id-equiv-fibered-double-Σ-Decomposition) = id-equiv
  pr1 (pr2 (pr2 id-equiv-fibered-double-Σ-Decomposition)) x = id-equiv
  pr2 (pr2 (pr2 id-equiv-fibered-double-Σ-Decomposition)) = refl-htpy

  equiv-eq-fibered-double-Σ-Decomposition :
    ( D : fibered-double-Σ-decomposition l2 l3 l4 l5 A ) → ((pair X Y) ＝ D) →
    equiv-fibered-double-Σ-decomposition (pair X Y) D
  equiv-eq-fibered-double-Σ-Decomposition (.X , .Y) refl =
    id-equiv-fibered-double-Σ-Decomposition

  is-equiv-equiv-eq-fibered-double-Σ-Decomposition :
    ( D : fibered-double-Σ-decomposition l2 l3 l4 l5 A ) →
    is-equiv (equiv-eq-fibered-double-Σ-Decomposition D)
  is-equiv-equiv-eq-fibered-double-Σ-Decomposition =
    fundamental-theorem-id
      is-contr-total-equiv-fibered-double-Σ-Decomposition
      equiv-eq-fibered-double-Σ-Decomposition

  extensionality-fibered-double-Σ-Decomposition :
    ( D : fibered-double-Σ-decomposition l2 l3 l4 l5 A ) →
    ((pair X Y) ＝ D) ≃
    equiv-fibered-double-Σ-decomposition (pair X Y) D
  pr1 (extensionality-fibered-double-Σ-Decomposition D) =
    equiv-eq-fibered-double-Σ-Decomposition D
  pr2 (extensionality-fibered-double-Σ-Decomposition D) =
    is-equiv-equiv-eq-fibered-double-Σ-Decomposition D

  eq-equiv-fibered-double-Σ-Decomposition :
    ( D : fibered-double-Σ-decomposition l2 l3 l4 l5 A ) →
    (equiv-fibered-double-Σ-decomposition (pair X Y)  D) →
    ((pair X Y) ＝ D)
  eq-equiv-fibered-double-Σ-Decomposition D =
    map-inv-equiv
      (extensionality-fibered-double-Σ-Decomposition D)
```

#### Version 2

```agda
displayed-double-Σ-decomposition :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : UU l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
displayed-double-Σ-decomposition l2 l3 l4 l5 A =
  ( Σ (Σ-Decomposition l2 l3 A)
  (λ D → (u : indexing-type-Σ-Decomposition D) →  Σ-Decomposition l4 l5 (cotype-Σ-Decomposition D u)))

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : displayed-double-Σ-decomposition l2 l3 l4 l5 A)
  where

  fst-displayed-double-Σ-decomposition : Σ-Decomposition l2 l3 A
  fst-displayed-double-Σ-decomposition = pr1 X

  indexing-type-fst-displayed-double-Σ-decomposition : UU l2
  indexing-type-fst-displayed-double-Σ-decomposition =
    indexing-type-Σ-Decomposition fst-displayed-double-Σ-decomposition

  cotype-fst-displayed-double-Σ-decomposition :
    indexing-type-fst-displayed-double-Σ-decomposition →
    UU l3
  cotype-fst-displayed-double-Σ-decomposition =
    cotype-Σ-Decomposition fst-displayed-double-Σ-decomposition

  map-matching-correspondence-fst-displayed-double-Σ-Decomposition :
    A →
    Σ (indexing-type-Σ-Decomposition fst-displayed-double-Σ-decomposition)
      (cotype-Σ-Decomposition fst-displayed-double-Σ-decomposition)
  map-matching-correspondence-fst-displayed-double-Σ-Decomposition  =
    map-matching-correspondence-Σ-Decomposition fst-displayed-double-Σ-decomposition

  snd-displayed-double-Σ-decomposition :
    ( x : indexing-type-fst-displayed-double-Σ-decomposition) →
    Σ-Decomposition l4 l5 (cotype-fst-displayed-double-Σ-decomposition x)
  snd-displayed-double-Σ-decomposition = pr2 X

  indexing-type-snd-displayed-double-Σ-decomposition :
    ( x : indexing-type-fst-displayed-double-Σ-decomposition) →
    UU l4
  indexing-type-snd-displayed-double-Σ-decomposition x =
    indexing-type-Σ-Decomposition (snd-displayed-double-Σ-decomposition x)

  cotype-snd-displayed-double-Σ-decomposition :
    ( x : indexing-type-fst-displayed-double-Σ-decomposition) →
    indexing-type-snd-displayed-double-Σ-decomposition x →
    UU l5
  cotype-snd-displayed-double-Σ-decomposition x =
   cotype-Σ-Decomposition (snd-displayed-double-Σ-decomposition x)

  map-matching-correspondence-snd-displayed-double-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-double-Σ-decomposition) →
    cotype-fst-displayed-double-Σ-decomposition x →
    Σ ( indexing-type-snd-displayed-double-Σ-decomposition x)
      ( cotype-snd-displayed-double-Σ-decomposition x)
  map-matching-correspondence-snd-displayed-double-Σ-Decomposition x =
    map-matching-correspondence-Σ-Decomposition (snd-displayed-double-Σ-decomposition x)
```

#### Characterization of identity type for version 2

```agda
-- module _
--   {l1 : Level} {l2 l3 l4 l5 l6 l7 l8 l9 : Level}
--   {A : UU l1} (X : fibered-double-Σ-decomposition l2 l3 l4 l5 A)
--   (Y : fibered-double-Σ-decomposition l6 l7 l8 l9 A)
--   where

--   type-equiv-fst-fibered-double-Σ-decomposition :
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
--   type-equiv-fst-fibered-double-Σ-decomposition =
--     equiv-Σ-Decomposition
--     (fst-fibered-double-Σ-decomposition X)
--     (fst-fibered-double-Σ-decomposition Y)

--   type-equiv-snd-fibered-double-Σ-decomposition :
--     (e : type-equiv-fst-fibered-double-Σ-decomposition) →
--     UU (l2 ⊔ l4 ⊔ l5 ⊔ l8 ⊔ l9)
--   type-equiv-snd-fibered-double-Σ-decomposition e =
--      Σ ( indexing-type-snd-fibered-double-Σ-decomposition X ≃
--          indexing-type-snd-fibered-double-Σ-decomposition Y)
--         λ f →
--           Σ ( (u : indexing-type-snd-fibered-double-Σ-decomposition X) →
--               cotype-snd-fibered-double-Σ-decomposition X u ≃
--               cotype-snd-fibered-double-Σ-decomposition Y ((map-equiv f) u))
--             ( λ g →
--               ( map-equiv (equiv-Σ (cotype-snd-fibered-double-Σ-decomposition Y) f g) ∘
--                 ( map-matching-correspondence-snd-fibered-double-Σ-Decomposition X))
--               ~
--               ( ( map-matching-correspondence-snd-fibered-double-Σ-Decomposition Y) ∘
--                 map-equiv (pr1 e)))

--   equiv-fibered-double-Σ-decomposition :
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
--   equiv-fibered-double-Σ-decomposition =
--     Σ ( type-equiv-fst-fibered-double-Σ-decomposition)
--       ( type-equiv-snd-fibered-double-Σ-decomposition)

--   fst-equiv-fibered-double-Σ-decomposition :
--     (e : equiv-fibered-double-Σ-decomposition) →
--     type-equiv-fst-fibered-double-Σ-decomposition
--   fst-equiv-fibered-double-Σ-decomposition = pr1

--   snd-equiv-fibered-double-Σ-decomposition :
--     (e : equiv-fibered-double-Σ-decomposition) →
--     type-equiv-snd-fibered-double-Σ-decomposition
--       (fst-equiv-fibered-double-Σ-decomposition e)
--   snd-equiv-fibered-double-Σ-decomposition = pr2

-- module _
--   { l1 l2 l3 l4 l5 : Level}  {A : UU l1}
--   ( (X , Y) : fibered-double-Σ-decomposition l2 l3 l4 l5 A)
--   where

--   is-contr-total-equiv-fibered-double-Σ-Decomposition :
--     is-contr ( Σ ( fibered-double-Σ-decomposition l2 l3 l4 l5 A )
--           (equiv-fibered-double-Σ-decomposition (pair X Y)))
--   is-contr-total-equiv-fibered-double-Σ-Decomposition =
--     is-contr-total-Eq-structure
--       ( λ X' Y' e → type-equiv-snd-fibered-double-Σ-decomposition
--         (pair X Y) (pair X' Y') e)
--       ( is-contr-total-equiv-Σ-Decomposition X)
--       ( pair X (id-equiv-Σ-Decomposition X))
--       ( is-contr-total-Eq-structure
--         ( λ U Vs e →
--           ( Σ ( (u : indexing-type-Σ-Decomposition Y) →
--                cotype-Σ-Decomposition Y u ≃
--                type-Inhabited-Type (pr1 Vs (map-equiv e u)))
--              ( λ f →
--                 ( ( map-equiv (equiv-Σ (λ u → type-Inhabited-Type (pr1 Vs u)) e f) ∘
--                   ( map-matching-correspondence-Σ-Decomposition Y)) ~
--                   (map-equiv (pr2 Vs))
--                   ))))
--         ( is-contr-total-equiv (indexing-type-Σ-Decomposition Y))
--         ( pair (indexing-type-Σ-Decomposition Y) id-equiv )
--         ( is-contr-total-Eq-structure
--            ( λ V f g →
--              ( map-equiv
--                ( equiv-Σ ( λ u → type-Inhabited-Type (V  u)) id-equiv g)
--               ∘  map-equiv (matching-correspondence-Σ-Decomposition Y)) ~
--               ( pr1 f)
--              )
--            ( is-contr-total-equiv-Fam-Inhabited-Types
--              ( inhabited-cotype-Σ-Decomposition Y))
--            ( pair
--              ( inhabited-cotype-Σ-Decomposition Y)
--              ( id-equiv-Fam-Inhabited-Types (inhabited-cotype-Σ-Decomposition Y)))
--              ( is-contr-total-htpy-equiv (matching-correspondence-Σ-Decomposition Y) )))

--   id-equiv-fibered-double-Σ-Decomposition :
--     equiv-fibered-double-Σ-decomposition (pair X Y) (pair X Y)
--   pr1 id-equiv-fibered-double-Σ-Decomposition = id-equiv-Σ-Decomposition X
--   pr1 (pr2 id-equiv-fibered-double-Σ-Decomposition) = id-equiv
--   pr1 (pr2 (pr2 id-equiv-fibered-double-Σ-Decomposition)) x = id-equiv
--   pr2 (pr2 (pr2 id-equiv-fibered-double-Σ-Decomposition)) = refl-htpy

--   equiv-eq-fibered-double-Σ-Decomposition :
--     ( D : fibered-double-Σ-decomposition l2 l3 l4 l5 A ) → ((pair X Y) ＝ D) →
--     equiv-fibered-double-Σ-decomposition (pair X Y) D
--   equiv-eq-fibered-double-Σ-Decomposition (.X , .Y) refl =
--     id-equiv-fibered-double-Σ-Decomposition

--   is-equiv-equiv-eq-fibered-double-Σ-Decomposition :
--     ( D : fibered-double-Σ-decomposition l2 l3 l4 l5 A ) →
--     is-equiv (equiv-eq-fibered-double-Σ-Decomposition D)
--   is-equiv-equiv-eq-fibered-double-Σ-Decomposition =
--     fundamental-theorem-id
--       is-contr-total-equiv-fibered-double-Σ-Decomposition
--       equiv-eq-fibered-double-Σ-Decomposition

--   extensionality-fibered-double-Σ-Decomposition :
--     ( D : fibered-double-Σ-decomposition l2 l3 l4 l5 A ) →
--     ((pair X Y) ＝ D) ≃
--     equiv-fibered-double-Σ-decomposition (pair X Y) D
--   pr1 (extensionality-fibered-double-Σ-Decomposition D) =
--     equiv-eq-fibered-double-Σ-Decomposition D
--   pr2 (extensionality-fibered-double-Σ-Decomposition D) =
--     is-equiv-equiv-eq-fibered-double-Σ-Decomposition D

--   eq-equiv-fibered-double-Σ-Decomposition :
--     ( D : fibered-double-Σ-decomposition l2 l3 l4 l5 A ) →
--     (equiv-fibered-double-Σ-decomposition (pair X Y)  D) →
--     ((pair X Y) ＝ D)
--   eq-equiv-fibered-double-Σ-Decomposition D =
--     map-inv-equiv
--       (extensionality-fibered-double-Σ-Decomposition D)
-- ```

-- #### Equivalence between version 1 and version 2



-- ```agda
-- --   equiv-Σ-Σ : {l1 l2 l3 : Level} → (A : UU l1) → (B : A → UU l2) → (C : Σ A B → UU l3) →
-- --     (Σ (Σ A B) C ≃ Σ A (λ a → Σ (B a ) (λ b → C (a , b))))
-- --   pr1 (equiv-Σ-Σ A B C) = λ ((a , b), c) → (a , (b , c))
-- --   pr2 (equiv-Σ-Σ A B C) = is-equiv-has-inverse (λ (a , (b , c)) → ((a , b), c)) (λ _ → refl) λ _ → refl

-- --   equiv-1 : {l1 l2 l3 l4 : Level} → (X : UU l1) → (U : UU l2) → (V : U → UU l3) → (Y : X → UU l4) → (f : X ≃ Σ U V) → (Σ X Y ≃ Σ U (λ u → Σ (V u) (λ v → Y (map-inv-equiv f (u , v))) ))
-- --   equiv-1  X U V Y f =
-- --     equivalence-reasoning
-- --       Σ X Y ≃ Σ (Σ U V) (λ w → Y (map-inv-equiv f w)) by inv-equiv ((equiv-Σ-equiv-base Y (inv-equiv f)))
-- --             ≃ Σ U (λ u → Σ (V u) (λ v → Y (map-inv-equiv f (u , v)))) by equiv-Σ-Σ _ _ _

-- --   equiv-2 : {l1 : Level} → (l2 l3 l4 l5 : Level) → (A : UU l1) →
-- --     ( Σ (Σ-Decomposition {!!} {!!} A)
-- --         (λ D → Σ-Decomposition {!!} {!!} (indexing-type-Σ-Decomposition D))
-- --       ≃
-- --       Σ (Σ-Decomposition {!!} {!!} A)
-- --         (λ D →
-- --         ( (m : indexing-type-Σ-Decomposition D) → Σ-Decomposition {!!} {!!} ((cotype-Σ-Decomposition D) m) )))
-- --   pr1 (equiv-2 l2 l3 l4 l5 A) ((X , Y , e), (U , V , f))  =
-- --     ( (U ,
-- --       (λ u → ( Σ (type-Inhabited-Type (V u))
-- --         ( λ v → type-Inhabited-Type (Y (map-inv-equiv f (u , v) ))) ,
-- --           {!!} )) ,
-- --       ( equiv-1 _ _ _ _ f ∘e e)) ,
-- --       λ (u : U) →
-- --         ( type-Inhabited-Type (V u) ,
-- --           (λ (v : type-Inhabited-Type (V (u))) → Y (map-inv-equiv f (u , v))) ,
-- --           id-equiv   ))
-- --   pr1 (pr1 (pr2 (equiv-2 l2 l3 l4 l5 A))) ((M , N , S) , D) = ( (Σ M (pr1 ∘ D) , ((λ (m , p) → (pr1 (pr2 (D m))) p) , {!!})) , M , ((λ m → (pr1  (D m) , {!!})) , id-equiv) )
-- --   pr2 (pr1 (pr2 (equiv-2 l2 l3 l4 l5 A))) ((M , N , S) , D) =
-- --     equational-reasoning
-- --       (pr1 (equiv-2 l2 l3 l4 l5 A) ∘
-- --          pr1 (pr1 (pr2 (equiv-2 l2 l3 l4 l5 A))))
-- --         ((M , N , S) , D) ＝ {!!} by {!!}
-- --   pr1 (pr2 (pr2 (equiv-2 l2 l3 l4 l5 A))) ((M , N , S) , D) = ( (Σ M (pr1 ∘ D) , ((λ (m , p) → (pr1 (pr2 (D m))) p) , {!!})) , M , ((λ m → (pr1  (D m) , {!!})) , id-equiv) )
-- --   pr2 (pr2 (pr2 (equiv-2 l2 l3 l4 l5 A))) ((X , Y , e) , (U , V , f))= {!!}
  
-- -- ```
