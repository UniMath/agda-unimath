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

#### Fibered double Σ-decompositions

```agda
fibered-double-Σ-Decomposition :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : UU l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
fibered-double-Σ-Decomposition l2 l3 l4 l5 A =
  ( Σ (Σ-Decomposition l2 l3 A)
  ( λ D → Σ-Decomposition l4 l5 (indexing-type-Σ-Decomposition D)))

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : fibered-double-Σ-Decomposition l2 l3 l4 l5 A)
  where

  fst-fibered-double-Σ-Decomposition : Σ-Decomposition l2 l3 A
  fst-fibered-double-Σ-Decomposition = pr1 X

  indexing-type-fst-fibered-double-Σ-Decomposition : UU l2
  indexing-type-fst-fibered-double-Σ-Decomposition =
    indexing-type-Σ-Decomposition fst-fibered-double-Σ-Decomposition

  inhabited-cotype-fst-fibered-double-Σ-Decomposition :
    indexing-type-fst-fibered-double-Σ-Decomposition → Inhabited-Type l3
  inhabited-cotype-fst-fibered-double-Σ-Decomposition =
    inhabited-cotype-Σ-Decomposition fst-fibered-double-Σ-Decomposition

  cotype-fst-fibered-double-Σ-Decomposition :
    indexing-type-fst-fibered-double-Σ-Decomposition → UU l3
  cotype-fst-fibered-double-Σ-Decomposition =
    cotype-Σ-Decomposition fst-fibered-double-Σ-Decomposition

  matching-correspondence-fst-fibered-double-Σ-Decomposition :
    A ≃
    Σ (indexing-type-Σ-Decomposition fst-fibered-double-Σ-Decomposition)
      (cotype-Σ-Decomposition fst-fibered-double-Σ-Decomposition)
  matching-correspondence-fst-fibered-double-Σ-Decomposition =
    matching-correspondence-Σ-Decomposition fst-fibered-double-Σ-Decomposition

  map-matching-correspondence-fst-fibered-double-Σ-Decomposition :
    A →
    Σ (indexing-type-Σ-Decomposition fst-fibered-double-Σ-Decomposition)
      (cotype-Σ-Decomposition fst-fibered-double-Σ-Decomposition)
  map-matching-correspondence-fst-fibered-double-Σ-Decomposition  =
    map-matching-correspondence-Σ-Decomposition
      fst-fibered-double-Σ-Decomposition

  snd-fibered-double-Σ-Decomposition :
      Σ-Decomposition l4 l5 indexing-type-fst-fibered-double-Σ-Decomposition
  snd-fibered-double-Σ-Decomposition = pr2 X

  indexing-type-snd-fibered-double-Σ-Decomposition : UU l4
  indexing-type-snd-fibered-double-Σ-Decomposition =
    indexing-type-Σ-Decomposition snd-fibered-double-Σ-Decomposition

  inhabited-cotype-snd-fibered-double-Σ-Decomposition :
    indexing-type-snd-fibered-double-Σ-Decomposition → Inhabited-Type l5
  inhabited-cotype-snd-fibered-double-Σ-Decomposition =
    inhabited-cotype-Σ-Decomposition snd-fibered-double-Σ-Decomposition

  cotype-snd-fibered-double-Σ-Decomposition :
    indexing-type-snd-fibered-double-Σ-Decomposition → UU l5
  cotype-snd-fibered-double-Σ-Decomposition =
    cotype-Σ-Decomposition snd-fibered-double-Σ-Decomposition

  matching-correspondence-snd-fibered-double-Σ-Decomposition :
    indexing-type-fst-fibered-double-Σ-Decomposition ≃
    Σ (indexing-type-Σ-Decomposition snd-fibered-double-Σ-Decomposition)
      (cotype-Σ-Decomposition snd-fibered-double-Σ-Decomposition)
  matching-correspondence-snd-fibered-double-Σ-Decomposition =
    matching-correspondence-Σ-Decomposition snd-fibered-double-Σ-Decomposition

  map-matching-correspondence-snd-fibered-double-Σ-Decomposition :
    indexing-type-fst-fibered-double-Σ-Decomposition →
    Σ (indexing-type-Σ-Decomposition snd-fibered-double-Σ-Decomposition)
      (cotype-Σ-Decomposition snd-fibered-double-Σ-Decomposition)
  map-matching-correspondence-snd-fibered-double-Σ-Decomposition =
    map-matching-correspondence-Σ-Decomposition
      snd-fibered-double-Σ-Decomposition
```

#### Displayed double Σ-decompositions

```agda
displayed-double-Σ-Decomposition :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : UU l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
displayed-double-Σ-Decomposition l2 l3 l4 l5 A =
  ( Σ (Σ-Decomposition l2 l3 A)
  (λ D → (u : indexing-type-Σ-Decomposition D) →  Σ-Decomposition l4 l5 (cotype-Σ-Decomposition D u)))

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : displayed-double-Σ-Decomposition l2 l3 l4 l5 A)
  where

  fst-displayed-double-Σ-Decomposition : Σ-Decomposition l2 l3 A
  fst-displayed-double-Σ-Decomposition = pr1 X

  indexing-type-fst-displayed-double-Σ-Decomposition : UU l2
  indexing-type-fst-displayed-double-Σ-Decomposition =
    indexing-type-Σ-Decomposition fst-displayed-double-Σ-Decomposition

  inhabited-cotype-fst-displayed-double-Σ-Decomposition :
    indexing-type-fst-displayed-double-Σ-Decomposition → Inhabited-Type l3
  inhabited-cotype-fst-displayed-double-Σ-Decomposition =
    inhabited-cotype-Σ-Decomposition fst-displayed-double-Σ-Decomposition

  cotype-fst-displayed-double-Σ-Decomposition :
    indexing-type-fst-displayed-double-Σ-Decomposition → UU l3
  cotype-fst-displayed-double-Σ-Decomposition =
    cotype-Σ-Decomposition fst-displayed-double-Σ-Decomposition

  matching-correspondence-fst-displayed-double-Σ-Decomposition :
    A ≃
    Σ (indexing-type-Σ-Decomposition fst-displayed-double-Σ-Decomposition)
      (cotype-Σ-Decomposition fst-displayed-double-Σ-Decomposition)
  matching-correspondence-fst-displayed-double-Σ-Decomposition  =
    matching-correspondence-Σ-Decomposition
      fst-displayed-double-Σ-Decomposition

  map-matching-correspondence-fst-displayed-double-Σ-Decomposition :
    A →
    Σ (indexing-type-Σ-Decomposition fst-displayed-double-Σ-Decomposition)
      (cotype-Σ-Decomposition fst-displayed-double-Σ-Decomposition)
  map-matching-correspondence-fst-displayed-double-Σ-Decomposition  =
    map-matching-correspondence-Σ-Decomposition
      fst-displayed-double-Σ-Decomposition

  snd-displayed-double-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-double-Σ-Decomposition) →
    Σ-Decomposition l4 l5 (cotype-fst-displayed-double-Σ-Decomposition x)
  snd-displayed-double-Σ-Decomposition = pr2 X

  indexing-type-snd-displayed-double-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-double-Σ-Decomposition) →
    UU l4
  indexing-type-snd-displayed-double-Σ-Decomposition x =
    indexing-type-Σ-Decomposition (snd-displayed-double-Σ-Decomposition x)

  inhabited-cotype-snd-displayed-double-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-double-Σ-Decomposition) →
    indexing-type-snd-displayed-double-Σ-Decomposition x → Inhabited-Type l5
  inhabited-cotype-snd-displayed-double-Σ-Decomposition x =
    inhabited-cotype-Σ-Decomposition (snd-displayed-double-Σ-Decomposition x)

  cotype-snd-displayed-double-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-double-Σ-Decomposition) →
    indexing-type-snd-displayed-double-Σ-Decomposition x →
    UU l5
  cotype-snd-displayed-double-Σ-Decomposition x =
    cotype-Σ-Decomposition (snd-displayed-double-Σ-Decomposition x)

  matching-correspondence-snd-displayed-double-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-double-Σ-Decomposition) →
    ( cotype-fst-displayed-double-Σ-Decomposition x ≃
      Σ ( indexing-type-snd-displayed-double-Σ-Decomposition x)
        ( cotype-snd-displayed-double-Σ-Decomposition x))
  matching-correspondence-snd-displayed-double-Σ-Decomposition x =
    matching-correspondence-Σ-Decomposition
      ( snd-displayed-double-Σ-Decomposition x)

  map-matching-correspondence-snd-displayed-double-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-double-Σ-Decomposition) →
    cotype-fst-displayed-double-Σ-Decomposition x →
    Σ ( indexing-type-snd-displayed-double-Σ-Decomposition x)
      ( cotype-snd-displayed-double-Σ-Decomposition x)
  map-matching-correspondence-snd-displayed-double-Σ-Decomposition x =
    map-matching-correspondence-Σ-Decomposition
      ( snd-displayed-double-Σ-Decomposition x)
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
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : Σ-Decomposition l2 l3 A) (Y : Σ-Decomposition l4 l5 A)
  (e : equiv-Σ-Decomposition X Y)
  where
  
  equiv-indexing-type-equiv-Σ-Decomposition :
    indexing-type-Σ-Decomposition X ≃ indexing-type-Σ-Decomposition Y
  equiv-indexing-type-equiv-Σ-Decomposition = pr1 e

  map-equiv-indexing-type-equiv-Σ-Decomposition :
    indexing-type-Σ-Decomposition X → indexing-type-Σ-Decomposition Y
  map-equiv-indexing-type-equiv-Σ-Decomposition =
    map-equiv equiv-indexing-type-equiv-Σ-Decomposition

  equiv-cotype-equiv-Σ-Decomposition :
    (x : indexing-type-Σ-Decomposition X) →
    cotype-Σ-Decomposition X x ≃
    cotype-Σ-Decomposition Y (map-equiv-indexing-type-equiv-Σ-Decomposition x)
  equiv-cotype-equiv-Σ-Decomposition = pr1 (pr2 e)

  map-equiv-cotype-equiv-Σ-Decomposition :
    (x : indexing-type-Σ-Decomposition X) →
    cotype-Σ-Decomposition X x →
    cotype-Σ-Decomposition Y (map-equiv-indexing-type-equiv-Σ-Decomposition x)
  map-equiv-cotype-equiv-Σ-Decomposition x =
    map-equiv (equiv-cotype-equiv-Σ-Decomposition x)
  
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

### Invariance of Σ-decompositions under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  equiv-tr-Σ-Decomposition :
    {l3 l4 : Level} → Σ-Decomposition l3 l4 A ≃ Σ-Decomposition l3 l4 B
  equiv-tr-Σ-Decomposition =
    equiv-tot
      ( λ X →
        equiv-tot
          ( λ Y →
            equiv-precomp-equiv (inv-equiv e) (total-Fam-Inhabited-Types Y)))

  map-equiv-tr-Σ-Decomposition :
    {l3 l4 : Level} → Σ-Decomposition l3 l4 A → Σ-Decomposition l3 l4 B
  map-equiv-tr-Σ-Decomposition = map-equiv equiv-tr-Σ-Decomposition
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
    is-contr
      ( Σ ( Set-Indexed-Σ-Decomposition l2 l3 A)
          ( equiv-Set-Indexed-Σ-Decomposition X))
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

#### Characterization of identity type for fibered double Σ-decompositions

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (X : fibered-double-Σ-Decomposition l2 l3 l4 l5 A)
  (Y : fibered-double-Σ-Decomposition l6 l7 l8 l9 A)
  where

  equiv-fst-fibered-double-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
  equiv-fst-fibered-double-Σ-Decomposition =
    equiv-Σ-Decomposition
    ( fst-fibered-double-Σ-Decomposition X)
    ( fst-fibered-double-Σ-Decomposition Y)

  equiv-snd-fibered-double-Σ-Decomposition :
    (e : equiv-fst-fibered-double-Σ-Decomposition) →
    UU (l4 ⊔ l5 ⊔ l6 ⊔ l8 ⊔ l9)
  equiv-snd-fibered-double-Σ-Decomposition e =
    equiv-Σ-Decomposition
      ( map-equiv-tr-Σ-Decomposition
        ( equiv-indexing-type-equiv-Σ-Decomposition
          ( fst-fibered-double-Σ-Decomposition X)
          ( fst-fibered-double-Σ-Decomposition Y)
          ( e))
        ( snd-fibered-double-Σ-Decomposition X))
      ( snd-fibered-double-Σ-Decomposition Y)

  equiv-fibered-double-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-fibered-double-Σ-Decomposition =
    Σ ( equiv-fst-fibered-double-Σ-Decomposition)
      ( equiv-snd-fibered-double-Σ-Decomposition)

  fst-equiv-fibered-double-Σ-Decomposition :
    (e : equiv-fibered-double-Σ-Decomposition) →
    equiv-fst-fibered-double-Σ-Decomposition
  fst-equiv-fibered-double-Σ-Decomposition = pr1

  snd-equiv-fibered-double-Σ-Decomposition :
    (e : equiv-fibered-double-Σ-Decomposition) →
    equiv-snd-fibered-double-Σ-Decomposition
      (fst-equiv-fibered-double-Σ-Decomposition e)
  snd-equiv-fibered-double-Σ-Decomposition = pr2

module _
  { l1 l2 l3 l4 l5 : Level}  {A : UU l1}
  ( D : fibered-double-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = fst-fibered-double-Σ-Decomposition D
    Y = snd-fibered-double-Σ-Decomposition D

  is-contr-total-equiv-fibered-double-Σ-Decomposition :
    is-contr
      ( Σ ( fibered-double-Σ-Decomposition l2 l3 l4 l5 A)
          ( equiv-fibered-double-Σ-Decomposition D))
  is-contr-total-equiv-fibered-double-Σ-Decomposition =
    is-contr-total-Eq-structure
      ( λ X' Y' e →
        equiv-snd-fibered-double-Σ-Decomposition D (X' , Y') e)
      ( is-contr-total-equiv-Σ-Decomposition X)
      ( X , id-equiv-Σ-Decomposition X)
      ( is-contr-total-Eq-structure
        ( λ U Vs e →
          ( Σ ( ( u : indexing-type-Σ-Decomposition Y) →
                cotype-Σ-Decomposition Y u ≃
                type-Inhabited-Type (pr1 Vs (map-equiv e u)))
             ( λ f →
               ( ( ( map-equiv-Σ (λ u → type-Inhabited-Type (pr1 Vs u)) e f) ∘
                   ( map-matching-correspondence-Σ-Decomposition Y)) ~
                 ( map-equiv (pr2 Vs))))))
        ( is-contr-total-equiv (indexing-type-Σ-Decomposition Y))
        ( pair (indexing-type-Σ-Decomposition Y) id-equiv )
        ( is-contr-total-Eq-structure
          ( λ V f g →
            ( ( map-equiv-Σ (λ u → type-Inhabited-Type (V  u)) id-equiv g) ∘
              ( map-matching-correspondence-Σ-Decomposition Y)) ~
              ( pr1 f))
          ( is-contr-total-equiv-Fam-Inhabited-Types
            ( inhabited-cotype-Σ-Decomposition Y))
          ( pair
            ( inhabited-cotype-Σ-Decomposition Y)
            ( id-equiv-Fam-Inhabited-Types
              ( inhabited-cotype-Σ-Decomposition Y)))
            ( is-contr-total-htpy-equiv
              ( matching-correspondence-Σ-Decomposition Y))))

  id-equiv-fibered-double-Σ-Decomposition :
    equiv-fibered-double-Σ-Decomposition D D
  pr1 id-equiv-fibered-double-Σ-Decomposition = id-equiv-Σ-Decomposition X
  pr1 (pr2 id-equiv-fibered-double-Σ-Decomposition) = id-equiv
  pr1 (pr2 (pr2 id-equiv-fibered-double-Σ-Decomposition)) x = id-equiv
  pr2 (pr2 (pr2 id-equiv-fibered-double-Σ-Decomposition)) = refl-htpy

  equiv-eq-fibered-double-Σ-Decomposition :
    (D' : fibered-double-Σ-Decomposition l2 l3 l4 l5 A ) →
    (D ＝ D') → equiv-fibered-double-Σ-Decomposition D D'
  equiv-eq-fibered-double-Σ-Decomposition .D refl =
    id-equiv-fibered-double-Σ-Decomposition

  is-equiv-equiv-eq-fibered-double-Σ-Decomposition :
    (D' : fibered-double-Σ-Decomposition l2 l3 l4 l5 A ) →
    is-equiv (equiv-eq-fibered-double-Σ-Decomposition D')
  is-equiv-equiv-eq-fibered-double-Σ-Decomposition =
    fundamental-theorem-id
      is-contr-total-equiv-fibered-double-Σ-Decomposition
      equiv-eq-fibered-double-Σ-Decomposition

  extensionality-fibered-double-Σ-Decomposition :
    (D' : fibered-double-Σ-Decomposition l2 l3 l4 l5 A) →
    (D ＝ D') ≃ equiv-fibered-double-Σ-Decomposition D D'
  pr1 (extensionality-fibered-double-Σ-Decomposition D') =
    equiv-eq-fibered-double-Σ-Decomposition D'
  pr2 (extensionality-fibered-double-Σ-Decomposition D') =
    is-equiv-equiv-eq-fibered-double-Σ-Decomposition D'

  eq-equiv-fibered-double-Σ-Decomposition :
    (D' : fibered-double-Σ-Decomposition l2 l3 l4 l5 A ) →
    (equiv-fibered-double-Σ-Decomposition D D') → (D ＝ D')
  eq-equiv-fibered-double-Σ-Decomposition D' =
    map-inv-equiv (extensionality-fibered-double-Σ-Decomposition D')
```

#### Characterization of identity type for displayed double Σ-decompositions

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (X : displayed-double-Σ-Decomposition l2 l3 l4 l5 A)
  (Y : displayed-double-Σ-Decomposition l6 l7 l8 l9 A)
  where

  equiv-fst-displayed-double-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
  equiv-fst-displayed-double-Σ-Decomposition =
    equiv-Σ-Decomposition
    ( fst-displayed-double-Σ-Decomposition X)
    ( fst-displayed-double-Σ-Decomposition Y)

  equiv-snd-displayed-double-Σ-Decomposition :
    (e : equiv-fst-displayed-double-Σ-Decomposition) →
    UU (l2 ⊔ l4 ⊔ l5 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-snd-displayed-double-Σ-Decomposition e =
    ( x : indexing-type-fst-displayed-double-Σ-Decomposition X) →
    equiv-Σ-Decomposition
      ( map-equiv-tr-Σ-Decomposition
        ( equiv-cotype-equiv-Σ-Decomposition
          ( fst-displayed-double-Σ-Decomposition X)
          ( fst-displayed-double-Σ-Decomposition Y)
          ( e)
          ( x))
        ( snd-displayed-double-Σ-Decomposition X x))
      ( snd-displayed-double-Σ-Decomposition Y
        ( map-equiv-indexing-type-equiv-Σ-Decomposition
          ( fst-displayed-double-Σ-Decomposition X)
          ( fst-displayed-double-Σ-Decomposition Y)
          ( e)
          ( x)))

  equiv-displayed-double-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-displayed-double-Σ-Decomposition =
    Σ ( equiv-fst-displayed-double-Σ-Decomposition)
      ( equiv-snd-displayed-double-Σ-Decomposition)

  fst-equiv-displayed-double-Σ-Decomposition :
    (e : equiv-displayed-double-Σ-Decomposition) →
    equiv-fst-displayed-double-Σ-Decomposition
  fst-equiv-displayed-double-Σ-Decomposition = pr1

  snd-equiv-displayed-double-Σ-Decomposition :
    (e : equiv-displayed-double-Σ-Decomposition) →
    equiv-snd-displayed-double-Σ-Decomposition
      ( fst-equiv-displayed-double-Σ-Decomposition e)
  snd-equiv-displayed-double-Σ-Decomposition = pr2

module _
  { l1 l2 l3 l4 l5 : Level}  {A : UU l1}
  ( disp-D : displayed-double-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = fst-displayed-double-Σ-Decomposition disp-D
    f_Y = snd-displayed-double-Σ-Decomposition disp-D

  is-contr-total-equiv-displayed-double-Σ-Decomposition :
    is-contr
      ( Σ ( displayed-double-Σ-Decomposition l2 l3 l4 l5 A )
          ( equiv-displayed-double-Σ-Decomposition disp-D))
  is-contr-total-equiv-displayed-double-Σ-Decomposition = 
    is-contr-total-Eq-structure
      ( λ X' f_Y' e → equiv-snd-displayed-double-Σ-Decomposition
        ( disp-D)
        ( pair X' f_Y')
        ( e))
      ( is-contr-total-equiv-Σ-Decomposition X)
      ( pair X (id-equiv-Σ-Decomposition X))
      ( is-contr-equiv
        ( Π-total-fam (λ x → _))
        ( inv-distributive-Π-Σ)
        ( is-contr-Π (λ x → is-contr-total-equiv-Σ-Decomposition (f_Y x))))

  id-equiv-displayed-double-Σ-Decomposition :
    equiv-displayed-double-Σ-Decomposition disp-D disp-D
  pr1 id-equiv-displayed-double-Σ-Decomposition = id-equiv-Σ-Decomposition X
  pr1 (pr2 id-equiv-displayed-double-Σ-Decomposition x) = id-equiv
  pr1 (pr2 (pr2 id-equiv-displayed-double-Σ-Decomposition x)) y = id-equiv
  pr2 (pr2 (pr2 id-equiv-displayed-double-Σ-Decomposition x)) = refl-htpy

  equiv-eq-displayed-double-Σ-Decomposition :
    (disp-D' : displayed-double-Σ-Decomposition l2 l3 l4 l5 A ) →
    (disp-D ＝ disp-D') → equiv-displayed-double-Σ-Decomposition disp-D disp-D'
  equiv-eq-displayed-double-Σ-Decomposition .disp-D refl =
    id-equiv-displayed-double-Σ-Decomposition

  is-equiv-equiv-eq-displayed-double-Σ-Decomposition :
    (disp-D' : displayed-double-Σ-Decomposition l2 l3 l4 l5 A ) →
    is-equiv (equiv-eq-displayed-double-Σ-Decomposition disp-D')
  is-equiv-equiv-eq-displayed-double-Σ-Decomposition =
    fundamental-theorem-id
      is-contr-total-equiv-displayed-double-Σ-Decomposition
      equiv-eq-displayed-double-Σ-Decomposition

  extensionality-displayed-double-Σ-Decomposition :
    (disp-D' : displayed-double-Σ-Decomposition l2 l3 l4 l5 A ) →
    (disp-D ＝ disp-D') ≃ equiv-displayed-double-Σ-Decomposition disp-D disp-D'
  pr1 (extensionality-displayed-double-Σ-Decomposition D) =
    equiv-eq-displayed-double-Σ-Decomposition D
  pr2 (extensionality-displayed-double-Σ-Decomposition D) =
    is-equiv-equiv-eq-displayed-double-Σ-Decomposition D

  eq-equiv-displayed-double-Σ-Decomposition :
    (disp-D' : displayed-double-Σ-Decomposition l2 l3 l4 l5 A ) →
    (equiv-displayed-double-Σ-Decomposition disp-D disp-D') → (disp-D ＝ disp-D')
  eq-equiv-displayed-double-Σ-Decomposition D =
    map-inv-equiv
      (extensionality-displayed-double-Σ-Decomposition D)
```

#### Equivalence between fibered double Σ-Decompositions and displayed double Σ-Decompositions

```agda

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (fib-D : fibered-double-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = indexing-type-fst-fibered-double-Σ-Decomposition fib-D
    Y = cotype-fst-fibered-double-Σ-Decomposition  fib-D
    e = matching-correspondence-Σ-Decomposition
      ( fst-fibered-double-Σ-Decomposition fib-D)
    U = indexing-type-snd-fibered-double-Σ-Decomposition fib-D
    V = cotype-snd-fibered-double-Σ-Decomposition fib-D
    f = matching-correspondence-Σ-Decomposition
      ( snd-fibered-double-Σ-Decomposition fib-D)

  matching-correspondence-displayed-fibered-double-Σ-Decomposition :
     A ≃ Σ U (λ u → Σ (V u) (λ v → Y (map-inv-equiv f (u , v))))
  matching-correspondence-displayed-fibered-double-Σ-Decomposition =
    equivalence-reasoning
    A ≃ Σ X Y by e
      ≃ Σ ( Σ U V) (λ uv → Y ((map-inv-equiv f) uv))
        by inv-equiv ( equiv-Σ-equiv-base Y (inv-equiv f))
      ≃ Σ U ( λ u → Σ (V u) (λ v → Y (map-inv-equiv f (u , v))))
        by assoc-Σ U V (λ uv → Y (map-inv-equiv f uv))

  map-displayed-fibered-double-Σ-Decomposition :
    displayed-double-Σ-Decomposition l4 (l3 ⊔ l5) l5 l3 A
  map-displayed-fibered-double-Σ-Decomposition  =
    ( ( U ,
      ( λ u → Σ (V u) (λ v → Y ((map-inv-equiv f) (u , v))) ,
        ind-trunc-Prop
          ( λ v → trunc-Prop (Σ (V u) (λ v → Y ((map-inv-equiv f) (u , v)))))
          ( λ v → ind-trunc-Prop
            ( λ y → trunc-Prop (Σ (V u) (λ v → Y ((map-inv-equiv f) (u , v)))))
            ( λ y → unit-trunc-Prop (v , y))
            ( is-inhabited-cotype-Σ-Decomposition
              ( fst-fibered-double-Σ-Decomposition fib-D)
              ( map-inv-equiv f (pair u v) )))
          ( is-inhabited-cotype-Σ-Decomposition
            ( snd-fibered-double-Σ-Decomposition fib-D) u) ) ,
      (  matching-correspondence-displayed-fibered-double-Σ-Decomposition)),
      ( λ u →
        ( V u) ,
        ( ( λ v →
          Y ((map-inv-equiv f) (pair u v)),
          ind-trunc-Prop
            ( λ y → trunc-Prop (Y ((map-inv-equiv f) (pair u v))))
            ( λ y → unit-trunc-Prop y)
            ( is-inhabited-cotype-Σ-Decomposition
              ( fst-fibered-double-Σ-Decomposition fib-D)
              ( map-inv-equiv f (pair u v)))),
        ( id-equiv))))

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (disp-D : displayed-double-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    M = indexing-type-fst-displayed-double-Σ-Decomposition disp-D
    N = cotype-fst-displayed-double-Σ-Decomposition disp-D
    s = matching-correspondence-Σ-Decomposition
      ( fst-displayed-double-Σ-Decomposition disp-D)
    P = indexing-type-snd-displayed-double-Σ-Decomposition disp-D
    Q = cotype-snd-displayed-double-Σ-Decomposition disp-D
    t = matching-correspondence-snd-displayed-double-Σ-Decomposition disp-D

  matching-correspondence-inv-displayed-fibered-double-Σ-Decomposition :
    A ≃ Σ (Σ M P) (λ (m , p) → Q m p)
  matching-correspondence-inv-displayed-fibered-double-Σ-Decomposition =
    equivalence-reasoning
    A ≃ Σ M N by s
      ≃ Σ M (λ m → Σ (P m) (Q m))by equiv-Σ (λ m → Σ (P m) (Q m)) id-equiv t
      ≃ Σ (Σ M P) (λ (m , p) → Q m p)
      by inv-assoc-Σ
        ( M)
        ( λ z → P z)
        ( λ z → Q (pr1 z) (pr2 z))

  map-inv-displayed-fibered-double-Σ-Decomposition :
    fibered-double-Σ-Decomposition (l2 ⊔ l4) l5 l2 l4 A
  map-inv-displayed-fibered-double-Σ-Decomposition =
    ( ( ( Σ M P) ,
        ( λ (m , p) →
          ( Q m p ,
            is-inhabited-cotype-Σ-Decomposition
              ( snd-displayed-double-Σ-Decomposition disp-D m)
              ( p))) ,
        ( matching-correspondence-inv-displayed-fibered-double-Σ-Decomposition )),
      ( M ,
        ( λ m → ( P m ,
            ind-trunc-Prop
              ( λ n → trunc-Prop (P m))
              ( λ n → unit-trunc-Prop (pr1 (map-equiv (t m) n)))
              ( is-inhabited-cotype-Σ-Decomposition
                ( fst-displayed-double-Σ-Decomposition disp-D)
                ( m)))) ,
        id-equiv))

module _
  {l1 l : Level} {A : UU l1}
  (fib-D : fibered-double-Σ-Decomposition l l l l A)
  where

  private
    X = indexing-type-fst-fibered-double-Σ-Decomposition fib-D
    Y = cotype-fst-fibered-double-Σ-Decomposition  fib-D
    e = matching-correspondence-Σ-Decomposition
      ( fst-fibered-double-Σ-Decomposition fib-D)
    U = indexing-type-snd-fibered-double-Σ-Decomposition fib-D
    V = cotype-snd-fibered-double-Σ-Decomposition fib-D
    f = matching-correspondence-Σ-Decomposition
      ( snd-fibered-double-Σ-Decomposition fib-D)
    disp-D = map-displayed-fibered-double-Σ-Decomposition fib-D
    M = indexing-type-fst-displayed-double-Σ-Decomposition disp-D
    N = cotype-fst-displayed-double-Σ-Decomposition disp-D
    s = matching-correspondence-Σ-Decomposition
      ( fst-displayed-double-Σ-Decomposition disp-D)
    P = indexing-type-snd-displayed-double-Σ-Decomposition disp-D
    Q = cotype-snd-displayed-double-Σ-Decomposition disp-D
    t = matching-correspondence-snd-displayed-double-Σ-Decomposition disp-D

    lemma : {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A ≃ B} →
      (f ＝ g) → map-equiv f ~ map-equiv g
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
        by lemma
          ( right-inverse-law-equiv (equiv-Σ-equiv-base Y (inv-equiv f)))
          ( map-equiv e a)

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
        ( id-equiv ,
        ( ( λ u → id-equiv) ,
          ( λ a → refl))))

module _
  {l1 l : Level} {A : UU l1}
  (disp-D : displayed-double-Σ-Decomposition l l l l A)
  where

  private
    M = indexing-type-fst-displayed-double-Σ-Decomposition disp-D
    N = cotype-fst-displayed-double-Σ-Decomposition disp-D
    s = matching-correspondence-Σ-Decomposition
      ( fst-displayed-double-Σ-Decomposition disp-D)
    P = indexing-type-snd-displayed-double-Σ-Decomposition disp-D
    Q = cotype-snd-displayed-double-Σ-Decomposition disp-D
    t = matching-correspondence-snd-displayed-double-Σ-Decomposition disp-D
    fib-D = map-inv-displayed-fibered-double-Σ-Decomposition disp-D
    X = indexing-type-fst-fibered-double-Σ-Decomposition fib-D
    Y = cotype-fst-fibered-double-Σ-Decomposition  fib-D
    e = matching-correspondence-Σ-Decomposition
      ( fst-fibered-double-Σ-Decomposition fib-D)
    U = indexing-type-snd-fibered-double-Σ-Decomposition fib-D
    V = cotype-snd-fibered-double-Σ-Decomposition fib-D
    f = matching-correspondence-Σ-Decomposition
      ( snd-fibered-double-Σ-Decomposition fib-D)

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
        refl-htpy
          ))

is-equiv-map-displayed-fibered-double-Σ-Decomposition :
  {l1 l : Level} → {A : UU l1} →
  is-equiv (map-displayed-fibered-double-Σ-Decomposition {l1} {l} {l} {l} {l} {A} )
is-equiv-map-displayed-fibered-double-Σ-Decomposition =
  ( ( map-inv-displayed-fibered-double-Σ-Decomposition , issec-map-inv-displayed-fibered-double-Σ-Decomposition) ,
    ( map-inv-displayed-fibered-double-Σ-Decomposition , isretr-map-inv-displayed-fibered-double-Σ-Decomposition))

equiv-displayed-fibered-double-Σ-Decomposition :
  {l1 , l : Level} → {A : UU l1} →
  fibered-double-Σ-Decomposition l l l l A ≃ displayed-double-Σ-Decomposition l l l l A
equiv-displayed-fibered-double-Σ-Decomposition =
  map-displayed-fibered-double-Σ-Decomposition ,
  is-equiv-map-displayed-fibered-double-Σ-Decomposition
```
