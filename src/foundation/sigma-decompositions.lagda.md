{{#title  Σ-decompositions of types}}

```agda
module foundation.sigma-decompositions where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.equivalence-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.sets
open import foundation.structure-identity-principle
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
