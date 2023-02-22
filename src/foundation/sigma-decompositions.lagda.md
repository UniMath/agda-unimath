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
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.transport
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
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

  matching-correspondence-snd-fibered-double-Σ-Decomposition :
    indexing-type-fst-fibered-double-Σ-decomposition ≃
    Σ (indexing-type-Σ-Decomposition snd-fibered-double-Σ-decomposition)
      (cotype-Σ-Decomposition snd-fibered-double-Σ-decomposition)
  matching-correspondence-snd-fibered-double-Σ-Decomposition =
    matching-correspondence-Σ-Decomposition snd-fibered-double-Σ-decomposition

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

  matching-correspondence-snd-displayed-double-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-double-Σ-decomposition) →
    ( cotype-fst-displayed-double-Σ-decomposition x ≃
      Σ ( indexing-type-snd-displayed-double-Σ-decomposition x)
        ( cotype-snd-displayed-double-Σ-decomposition x))
  matching-correspondence-snd-displayed-double-Σ-Decomposition x =
    matching-correspondence-Σ-Decomposition (snd-displayed-double-Σ-decomposition x)

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
module _
  {l1 : Level} {l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (X : displayed-double-Σ-decomposition l2 l3 l4 l5 A)
  (Y : displayed-double-Σ-decomposition l6 l7 l8 l9 A)
  where

  type-equiv-fst-displayed-double-Σ-decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
  type-equiv-fst-displayed-double-Σ-decomposition =
    equiv-Σ-Decomposition
    (fst-displayed-double-Σ-decomposition X)
    (fst-displayed-double-Σ-decomposition Y)

  type-equiv-snd-displayed-double-Σ-decomposition :
    (e : type-equiv-fst-displayed-double-Σ-decomposition) →
    UU (l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l8 ⊔ l9)
  type-equiv-snd-displayed-double-Σ-decomposition e =
     ( x : indexing-type-fst-displayed-double-Σ-decomposition X) →
     Σ ( indexing-type-snd-displayed-double-Σ-decomposition X x ≃
         indexing-type-snd-displayed-double-Σ-decomposition Y
           (map-equiv-indexing-type-equiv-Σ-Decomposition x))
        λ f →
          Σ ( (u : indexing-type-snd-displayed-double-Σ-decomposition X x) →
              cotype-snd-displayed-double-Σ-decomposition X x u ≃
              cotype-snd-displayed-double-Σ-decomposition Y
                (map-equiv-indexing-type-equiv-Σ-Decomposition x) ((map-equiv f) u))
            ( λ g →
              ( map-equiv (equiv-Σ (cotype-snd-displayed-double-Σ-decomposition Y
                ( map-equiv-indexing-type-equiv-Σ-Decomposition x)) f g) ∘
                ( map-matching-correspondence-snd-displayed-double-Σ-Decomposition X x))
              ~
              ( ( map-matching-correspondence-snd-displayed-double-Σ-Decomposition Y
                ( (map-equiv-indexing-type-equiv-Σ-Decomposition x)) ∘
                (map-equiv (pr1 (pr2 e) x)))))
     where
       map-equiv-indexing-type-equiv-Σ-Decomposition :
         indexing-type-fst-displayed-double-Σ-decomposition X →
         indexing-type-fst-displayed-double-Σ-decomposition Y
       map-equiv-indexing-type-equiv-Σ-Decomposition = (map-equiv (pr1 e))

  equiv-displayed-double-Σ-decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-displayed-double-Σ-decomposition =
    Σ ( type-equiv-fst-displayed-double-Σ-decomposition)
      ( type-equiv-snd-displayed-double-Σ-decomposition)

  fst-equiv-displayed-double-Σ-decomposition :
    (e : equiv-displayed-double-Σ-decomposition) →
    type-equiv-fst-displayed-double-Σ-decomposition
  fst-equiv-displayed-double-Σ-decomposition = pr1

  snd-equiv-displayed-double-Σ-decomposition :
    (e : equiv-displayed-double-Σ-decomposition) →
    type-equiv-snd-displayed-double-Σ-decomposition
      (fst-equiv-displayed-double-Σ-decomposition e)
  snd-equiv-displayed-double-Σ-decomposition = pr2

module _
  { l1 l2 l3 l4 l5 : Level}  {A : UU l1}
  ( (X , f_Y) : displayed-double-Σ-decomposition l2 l3 l4 l5 A)
  where

  is-contr-total-equiv-displayed-double-Σ-Decomposition :
    is-contr ( Σ ( displayed-double-Σ-decomposition l2 l3 l4 l5 A )
          (equiv-displayed-double-Σ-decomposition (pair X f_Y)))
  is-contr-total-equiv-displayed-double-Σ-Decomposition =
    is-contr-total-Eq-structure
      ( λ X' f_Y' e → type-equiv-snd-displayed-double-Σ-decomposition
        (pair X f_Y) (pair X' f_Y') e)
      ( is-contr-total-equiv-Σ-Decomposition X)
      ( pair X (id-equiv-Σ-Decomposition X))
      ( is-contr-equiv
        ( Π-total-fam (λ x → _))
        inv-distributive-Π-Σ
        ( is-contr-Π (λ x → is-contr-total-equiv-Σ-Decomposition (f_Y x))))

  id-equiv-displayed-double-Σ-Decomposition :
    equiv-displayed-double-Σ-decomposition (pair X f_Y) (pair X f_Y)
  pr1 id-equiv-displayed-double-Σ-Decomposition = id-equiv-Σ-Decomposition X
  pr1 (pr2 id-equiv-displayed-double-Σ-Decomposition x) = id-equiv
  pr1 (pr2 (pr2 id-equiv-displayed-double-Σ-Decomposition x)) y = id-equiv
  pr2 (pr2 (pr2 id-equiv-displayed-double-Σ-Decomposition x)) = refl-htpy

  equiv-eq-displayed-double-Σ-Decomposition :
    ( D : displayed-double-Σ-decomposition l2 l3 l4 l5 A ) → ((pair X f_Y) ＝ D) →
    equiv-displayed-double-Σ-decomposition (pair X f_Y) D
  equiv-eq-displayed-double-Σ-Decomposition (.X , .f_Y) refl =
    id-equiv-displayed-double-Σ-Decomposition

  is-equiv-equiv-eq-displayed-double-Σ-Decomposition :
    ( D : displayed-double-Σ-decomposition l2 l3 l4 l5 A ) →
    is-equiv (equiv-eq-displayed-double-Σ-Decomposition D)
  is-equiv-equiv-eq-displayed-double-Σ-Decomposition =
    fundamental-theorem-id
      is-contr-total-equiv-displayed-double-Σ-Decomposition
      equiv-eq-displayed-double-Σ-Decomposition

  extensionality-displayed-double-Σ-Decomposition :
    ( D : displayed-double-Σ-decomposition l2 l3 l4 l5 A ) →
    ((pair X f_Y) ＝ D) ≃
    equiv-displayed-double-Σ-decomposition (pair X f_Y) D
  pr1 (extensionality-displayed-double-Σ-Decomposition D) =
    equiv-eq-displayed-double-Σ-Decomposition D
  pr2 (extensionality-displayed-double-Σ-Decomposition D) =
    is-equiv-equiv-eq-displayed-double-Σ-Decomposition D

  eq-equiv-displayed-double-Σ-Decomposition :
    ( D : displayed-double-Σ-decomposition l2 l3 l4 l5 A ) →
    (equiv-displayed-double-Σ-decomposition (pair X f_Y)  D) →
    ((pair X f_Y) ＝ D)
  eq-equiv-displayed-double-Σ-Decomposition D =
    map-inv-equiv
      (extensionality-displayed-double-Σ-Decomposition D)
```

#### Equivalence between version 1 and version 2



```agda

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (fib-D : fibered-double-Σ-decomposition l2 l3 l4 l5 A)
  where

  private
    X : UU l2
    X = indexing-type-fst-fibered-double-Σ-decomposition fib-D

    Y : X → UU l3
    Y = cotype-fst-fibered-double-Σ-decomposition  fib-D

    e : A ≃ Σ X Y
    e = matching-correspondence-Σ-Decomposition (fst-fibered-double-Σ-decomposition fib-D)

    U : UU l4
    U = indexing-type-snd-fibered-double-Σ-decomposition fib-D

    V : U → UU l5
    V = cotype-snd-fibered-double-Σ-decomposition fib-D

    f : X ≃ Σ U V
    f = matching-correspondence-Σ-Decomposition (snd-fibered-double-Σ-decomposition fib-D)

  matching-correspondence-displayed-fibered-double-Σ-Decomposition :
     A ≃ Σ U (λ u → Σ (V u) (λ v → Y (map-inv-equiv f (u , v))))
  matching-correspondence-displayed-fibered-double-Σ-Decomposition =
    equivalence-reasoning
    A ≃ Σ X Y by e
      ≃ Σ ( Σ U V) (λ uv → Y ((map-inv-equiv f) uv))
        by inv-equiv ( equiv-Σ-equiv-base Y (inv-equiv f))
      ≃ Σ U ( λ u → Σ (V u) (λ v → Y (map-inv-equiv f (u , v))))
        by assoc-Σ _ _ _

  map-displayed-fibered-double-Σ-Decomposition :
    displayed-double-Σ-decomposition l4 (l3 ⊔ l5) l5 l3 A
  map-displayed-fibered-double-Σ-Decomposition  =
    ( ( U ,
        ( λ u → Σ (V u) (λ v → Y ((map-inv-equiv f) (u , v))) ,
           ind-trunc-Prop
             ( λ v → trunc-Prop (Σ (V u) (λ v → Y ((map-inv-equiv f) (u , v)))))
             ( λ v → ind-trunc-Prop
               ( λ y → trunc-Prop (Σ (V u) (λ v → Y ((map-inv-equiv f) (u , v)))))
               ( λ y → unit-trunc-Prop (v , y))
               ( is-inhabited-cotype-Σ-Decomposition (fst-fibered-double-Σ-decomposition fib-D) (map-inv-equiv f (pair u v) )))
             (is-inhabited-cotype-Σ-Decomposition (snd-fibered-double-Σ-decomposition fib-D) u) ) ,
      (  matching-correspondence-displayed-fibered-double-Σ-Decomposition)),
      ( λ u →
        ( V u) ,
        ( ( λ v →
              Y ((map-inv-equiv f) (pair u v)),
              ind-trunc-Prop
                ( λ y → trunc-Prop (Y ((map-inv-equiv f) (pair u v))))
                (λ y → unit-trunc-Prop y)
                  (is-inhabited-cotype-Σ-Decomposition (fst-fibered-double-Σ-decomposition fib-D) (map-inv-equiv f (pair u v)))),
        id-equiv)))

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (disp-D : displayed-double-Σ-decomposition l2 l3 l4 l5 A)
  where

  private
    M : UU l2
    M = indexing-type-fst-displayed-double-Σ-decomposition disp-D

    N : M → UU l3
    N = cotype-fst-displayed-double-Σ-decomposition disp-D

    s : A ≃ Σ M N
    s = matching-correspondence-Σ-Decomposition (fst-displayed-double-Σ-decomposition disp-D)

    P : M → UU l4
    P = indexing-type-snd-displayed-double-Σ-decomposition disp-D

    Q : (m : M) → P m → UU l5
    Q = cotype-snd-displayed-double-Σ-decomposition disp-D

    t : (m : M) → N m  ≃ Σ (P m) (Q m)
    t = matching-correspondence-snd-displayed-double-Σ-Decomposition disp-D

  matching-correspondence-inv-displayed-fibered-double-Σ-Decomposition :
    A ≃ Σ (Σ M P) (λ (m , p) → Q m p)
  matching-correspondence-inv-displayed-fibered-double-Σ-Decomposition =
    equivalence-reasoning
    A ≃ Σ M N by s
      ≃ Σ M (λ m → Σ (P m) (Q m))by equiv-Σ (λ m → Σ (P m) (Q m)) id-equiv t
      ≃ Σ (Σ M P) (λ (m , p) → Q m p) by inv-assoc-Σ _ _ _

  map-inv-displayed-fibered-double-Σ-Decomposition :
    fibered-double-Σ-decomposition (l2 ⊔ l4) l5 l2 l4 A
  map-inv-displayed-fibered-double-Σ-Decomposition =
    ( ( ( Σ M P) ,
        ( λ (m , p) →
          ( Q m p , is-inhabited-cotype-Σ-Decomposition (snd-displayed-double-Σ-decomposition disp-D m) p)) ,
        ( matching-correspondence-inv-displayed-fibered-double-Σ-Decomposition )),
      ( M ,
        ( λ m →
          ( P m ,
            ind-trunc-Prop
              (λ n → trunc-Prop (P m))
              (λ n → unit-trunc-Prop (pr1 (map-equiv (t m) n)))
              (is-inhabited-cotype-Σ-Decomposition (fst-displayed-double-Σ-decomposition disp-D) m))) ,
        id-equiv))

module _
  {l1 l : Level} {A : UU l1}
  (fib-D : fibered-double-Σ-decomposition l l l l A)
  where

  private
    X : UU l
    X = indexing-type-fst-fibered-double-Σ-decomposition fib-D

    Y : X → UU l
    Y = cotype-fst-fibered-double-Σ-decomposition  fib-D

    e : A ≃ Σ X Y
    e = matching-correspondence-Σ-Decomposition (fst-fibered-double-Σ-decomposition fib-D)

    U : UU l
    U = indexing-type-snd-fibered-double-Σ-decomposition fib-D

    V : U → UU l
    V = cotype-snd-fibered-double-Σ-decomposition fib-D

    f : X ≃ Σ U V
    f = matching-correspondence-Σ-Decomposition (snd-fibered-double-Σ-decomposition fib-D)

    disp-D : displayed-double-Σ-decomposition l l l l A
    disp-D = map-displayed-fibered-double-Σ-Decomposition fib-D

    M : UU l
    M = indexing-type-fst-displayed-double-Σ-decomposition disp-D

    N : M → UU l
    N = cotype-fst-displayed-double-Σ-decomposition disp-D

    s : A ≃ Σ M N
    s = matching-correspondence-Σ-Decomposition (fst-displayed-double-Σ-decomposition disp-D)

    P : M → UU l
    P = indexing-type-snd-displayed-double-Σ-decomposition disp-D

    Q : (m : M) → P m → UU l
    Q = cotype-snd-displayed-double-Σ-decomposition disp-D

    t : (m : M) → N m  ≃ Σ (P m) (Q m)
    t = matching-correspondence-snd-displayed-double-Σ-Decomposition disp-D

    lemma : {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A ≃ B} →
      (f ＝ g) → (a : A) → (map-equiv f a ＝ map-equiv g a)
    lemma refl a = refl

    htpy-matching-correspondence :
      map-equiv (
        ( equiv-Σ Y (inv-equiv f) (λ (m , p) → id-equiv)) ∘e
        matching-correspondence-inv-displayed-fibered-double-Σ-Decomposition
          (disp-D))
      ~ map-equiv e
    htpy-matching-correspondence a =
      equational-reasoning
      map-equiv
        ( equiv-Σ-equiv-base Y (inv-equiv f) ∘e
          inv-equiv ( equiv-Σ-equiv-base Y (inv-equiv f)))
        ( map-equiv e a) ＝ (map-equiv e a)
           by lemma (right-inverse-law-equiv (equiv-Σ-equiv-base Y (inv-equiv f)) ) (map-equiv e a)

  isretr-map-inv-displayed-fibered-double-Σ-Decomposition :
     map-inv-displayed-fibered-double-Σ-Decomposition
      ( map-displayed-fibered-double-Σ-Decomposition fib-D) ＝ fib-D
  isretr-map-inv-displayed-fibered-double-Σ-Decomposition =
    eq-equiv-fibered-double-Σ-Decomposition
      ( map-inv-displayed-fibered-double-Σ-Decomposition
        ( map-displayed-fibered-double-Σ-Decomposition fib-D))
      fib-D
      ( ( inv-equiv f  ,
          ( ( λ x → id-equiv) ,
          ( htpy-matching-correspondence))) ,
        ( id-equiv , ( (λ u → id-equiv) , (lemma (inv (right-inverse-law-equiv f))))))

module _
  {l1 l : Level} {A : UU l1}
  (disp-D : displayed-double-Σ-decomposition l l l l A)
  where

  private
    M : UU l
    M = indexing-type-fst-displayed-double-Σ-decomposition disp-D

    N : M → UU l
    N = cotype-fst-displayed-double-Σ-decomposition disp-D

    s : A ≃ Σ M N
    s = matching-correspondence-Σ-Decomposition (fst-displayed-double-Σ-decomposition disp-D)

    P : M → UU l
    P = indexing-type-snd-displayed-double-Σ-decomposition disp-D

    Q : (m : M) → P m → UU l
    Q = cotype-snd-displayed-double-Σ-decomposition disp-D

    t : (m : M) → N m  ≃ Σ (P m) (Q m)
    t = matching-correspondence-snd-displayed-double-Σ-Decomposition disp-D

    fib-D : fibered-double-Σ-decomposition l l l l A
    fib-D = map-inv-displayed-fibered-double-Σ-Decomposition disp-D

    X : UU l
    X = indexing-type-fst-fibered-double-Σ-decomposition fib-D

    Y : X → UU l
    Y = cotype-fst-fibered-double-Σ-decomposition  fib-D

    e : A ≃ Σ X Y
    e = matching-correspondence-Σ-Decomposition (fst-fibered-double-Σ-decomposition fib-D)

    U : UU l
    U = indexing-type-snd-fibered-double-Σ-decomposition fib-D

    V : U → UU l
    V = cotype-snd-fibered-double-Σ-decomposition fib-D

    f : X ≃ Σ U V
    f = matching-correspondence-Σ-Decomposition (snd-fibered-double-Σ-decomposition fib-D)

    lemma' : {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A ≃ B} →
      (f ＝ g) → (a : A) → (map-equiv f a ＝ map-equiv g a)
    lemma' refl a = refl

    lemma :
      {l : Level} {C : UU l} →
      (inv-equiv (id-equiv {l} {C})) ＝ id-equiv {l} {C}
    lemma = eq-htpy-equiv refl-htpy

    lemma2 :
      equiv-Σ-equiv-base Y (inv-equiv id-equiv) ＝ id-equiv
    lemma2 = eq-htpy-equiv refl-htpy

    lemma3 :
      inv-equiv (equiv-Σ-equiv-base Y (inv-equiv id-equiv)) ＝ id-equiv
    lemma3 = (ap inv-equiv lemma2)  ∙ lemma

    lemma4 :
       ( assoc-Σ M P Y  ∘e
         ( inv-equiv ( equiv-Σ-equiv-base Y (inv-equiv id-equiv)) ∘e
         inv-assoc-Σ M P Y )) ＝ id-equiv
    lemma4 = (ap (λ e → assoc-Σ M P Y ∘e (e ∘e inv-assoc-Σ M P Y)) lemma3) ∙ ((ap (λ e → assoc-Σ M P Y ∘e e) ( left-unit-law-equiv (inv-assoc-Σ M P Y))) ∙ eq-htpy-equiv (issec-map-inv-assoc-Σ M P Y))

    lemma5 :
      ( ( equiv-Σ N id-equiv (inv-equiv ∘ t) ) ∘e
        ( assoc-Σ M P Y  ∘e
        ( inv-equiv ( equiv-Σ-equiv-base Y (inv-equiv id-equiv)) ∘e
        ( inv-assoc-Σ M P Y ∘e
        ( equiv-Σ (λ m → Σ (P m) (Q m)) id-equiv t ∘e
          s ))))) ＝ s
    lemma5 =
      equational-reasoning
        ( ( equiv-Σ N id-equiv (inv-equiv ∘ t) ) ∘e
          ( assoc-Σ M P Y  ∘e
          ( inv-equiv ( equiv-Σ-equiv-base Y (inv-equiv id-equiv)) ∘e
          ( inv-assoc-Σ M P Y ∘e
          ( equiv-Σ (λ m → Σ (P m) (Q m)) id-equiv t ∘e
            s)))))
            ＝
        ( ( equiv-Σ N id-equiv (inv-equiv ∘ t) ) ∘e
          ( equiv-Σ (λ m → Σ (P m) (Q m)) id-equiv t ∘e
            s))
            by
            eq-htpy-equiv (λ a → ap (map-equiv (equiv-Σ N id-equiv (inv-equiv ∘ t)))
              ( lemma' lemma4 (map-equiv (( equiv-Σ (λ m → Σ (P m) (Q m)) id-equiv t )) (map-equiv s a))))
            ＝
        equiv-Σ N id-equiv (λ m → inv-equiv (t m) ∘e t m) ∘e s
            by eq-htpy-equiv refl-htpy
            ＝
        s
            by
            eq-htpy-equiv (λ a → (htpy-map-Σ N refl-htpy (λ m p → (((map-inv-equiv (t m)) ∘ map-equiv (t m)) p  )) λ m → lemma' (left-inverse-law-equiv (t m))) (map-equiv s a))

    htpy-matching-correspondence :
      map-equiv (
        ( equiv-Σ N id-equiv (inv-equiv ∘ t)  ) ∘e
        matching-correspondence-displayed-fibered-double-Σ-Decomposition
          (fib-D))
      ~ map-equiv s
    htpy-matching-correspondence a =
      equational-reasoning
        map-equiv
          ( ( equiv-Σ N id-equiv (inv-equiv ∘ t) ) ∘e
            ( assoc-Σ M P Y  ∘e
            ( inv-equiv ( equiv-Σ-equiv-base Y (inv-equiv id-equiv)) ∘e
            ( inv-assoc-Σ M P Y ∘e
            ( equiv-Σ (λ m → Σ (P m) (Q m)) id-equiv t ∘e
              s)))) ) a
          ＝
        map-equiv s a by
          lemma' lemma5 a

  issec-map-inv-displayed-fibered-double-Σ-Decomposition :
    ( map-displayed-fibered-double-Σ-Decomposition {l1} {l} {l} {l} {l} {A} fib-D) ＝ disp-D
  issec-map-inv-displayed-fibered-double-Σ-Decomposition =
     eq-equiv-displayed-double-Σ-Decomposition
      ( map-displayed-fibered-double-Σ-Decomposition fib-D )
      disp-D
      ( ( id-equiv ,
          ( ( inv-equiv ∘ t) ,
            htpy-matching-correspondence)) ,
        λ (m : M) → id-equiv ,
        ( ( λ (p : P m) → id-equiv ) ,
        λ ( pq : Σ (P m) (Q m)) →
          equational-reasoning
              pq ＝ map-equiv ((t m) ∘e inv-equiv (t m)) pq
            by lemma' (inv (right-inverse-law-equiv (t m))) pq
          ))

is-equiv-map-displayed-fibered-double-Σ-Decomposition :
  {l1 l : Level} → {A : UU l1} →
  is-equiv (map-displayed-fibered-double-Σ-Decomposition {l1} {l} {l} {l} {l} {A} )
is-equiv-map-displayed-fibered-double-Σ-Decomposition =
  ( ( map-inv-displayed-fibered-double-Σ-Decomposition , issec-map-inv-displayed-fibered-double-Σ-Decomposition) ,
    ( map-inv-displayed-fibered-double-Σ-Decomposition , isretr-map-inv-displayed-fibered-double-Σ-Decomposition))

equiv-displayed-fibered-double-Σ-Decomposition :
  {l1 , l : Level} → {A : UU l1} →
  fibered-double-Σ-decomposition l l l l A ≃ displayed-double-Σ-decomposition l l l l A
equiv-displayed-fibered-double-Σ-Decomposition =
  map-displayed-fibered-double-Σ-Decomposition ,
  is-equiv-map-displayed-fibered-double-Σ-Decomposition
```
