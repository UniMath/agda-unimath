# Σ-decompositions of types

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.sigma-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.transposition-identifications-along-equivalences
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

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

A **Σ-decomposition** of a type `A` consists of a type `X` and a family of
inhabited types `Y x` indexed by `x : A` equipped with an equivalence
`A ≃ Σ X Y`. The type `X` is called the indexing type of the Σ-decomposition,
the elements of `Y x` are called the cotypes of the Σ-decomposition, and the
equivalence `A ≃ Σ X Y` is the matching correspondence of the Σ-decomposition.

Note that types may have many Σ-decompositions. The type of Σ-decompositions of
the unit type, for instance, is equivalent to the type of all pointed connected
types. Alternatively, we may think of the type of Σ-decompositions of the unit
type as the type of higher groupoid structures on a point, i.e., the type of
higher group structures.

We may restrict to Σ-decompositions where the indexing type is in a given
subuniverse, such as the subuniverse of sets or the subuniverse of finite sets.
For instance, the type of set-indexed Σ-decompositions of a type `A` is
equivalent to the type of equivalence relations on `A`.

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

  is-inhabited-indexing-type-inhabited-Σ-Decomposition :
    (p : is-inhabited A) → (is-inhabited (indexing-type-Σ-Decomposition))
  is-inhabited-indexing-type-inhabited-Σ-Decomposition p =
    map-is-inhabited (pr1 ∘ map-matching-correspondence-Σ-Decomposition) p

  inhabited-indexing-type-inhabited-Σ-Decomposition :
    (p : is-inhabited A) → (Inhabited-Type l2)
  pr1 (inhabited-indexing-type-inhabited-Σ-Decomposition p) =
    indexing-type-Σ-Decomposition
  pr2 (inhabited-indexing-type-inhabited-Σ-Decomposition p) =
    is-inhabited-indexing-type-inhabited-Σ-Decomposition p

  is-inhabited-base-is-inhabited-indexing-type-Σ-Decomposition :
    (is-inhabited (indexing-type-Σ-Decomposition)) → (is-inhabited A)
  is-inhabited-base-is-inhabited-indexing-type-Σ-Decomposition p =
    map-is-inhabited
      ( map-inv-equiv matching-correspondence-Σ-Decomposition)
      ( is-inhabited-Σ p is-inhabited-cotype-Σ-Decomposition)
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

### Fibered double Σ-decompositions

```agda
fibered-Σ-Decomposition :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : UU l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
fibered-Σ-Decomposition l2 l3 l4 l5 A =
  Σ (Σ-Decomposition l2 l3 A)
    ( λ D → Σ-Decomposition l4 l5 (indexing-type-Σ-Decomposition D))

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : fibered-Σ-Decomposition l2 l3 l4 l5 A)
  where

  fst-fibered-Σ-Decomposition : Σ-Decomposition l2 l3 A
  fst-fibered-Σ-Decomposition = pr1 X

  indexing-type-fst-fibered-Σ-Decomposition : UU l2
  indexing-type-fst-fibered-Σ-Decomposition =
    indexing-type-Σ-Decomposition fst-fibered-Σ-Decomposition

  inhabited-cotype-fst-fibered-Σ-Decomposition :
    indexing-type-fst-fibered-Σ-Decomposition → Inhabited-Type l3
  inhabited-cotype-fst-fibered-Σ-Decomposition =
    inhabited-cotype-Σ-Decomposition fst-fibered-Σ-Decomposition

  cotype-fst-fibered-Σ-Decomposition :
    indexing-type-fst-fibered-Σ-Decomposition → UU l3
  cotype-fst-fibered-Σ-Decomposition =
    cotype-Σ-Decomposition fst-fibered-Σ-Decomposition

  matching-correspondence-fst-fibered-Σ-Decomposition :
    A ≃
    Σ (indexing-type-Σ-Decomposition fst-fibered-Σ-Decomposition)
      (cotype-Σ-Decomposition fst-fibered-Σ-Decomposition)
  matching-correspondence-fst-fibered-Σ-Decomposition =
    matching-correspondence-Σ-Decomposition fst-fibered-Σ-Decomposition

  map-matching-correspondence-fst-fibered-Σ-Decomposition :
    A →
    Σ (indexing-type-Σ-Decomposition fst-fibered-Σ-Decomposition)
      (cotype-Σ-Decomposition fst-fibered-Σ-Decomposition)
  map-matching-correspondence-fst-fibered-Σ-Decomposition =
    map-matching-correspondence-Σ-Decomposition
      fst-fibered-Σ-Decomposition

  snd-fibered-Σ-Decomposition :
      Σ-Decomposition l4 l5 indexing-type-fst-fibered-Σ-Decomposition
  snd-fibered-Σ-Decomposition = pr2 X

  indexing-type-snd-fibered-Σ-Decomposition : UU l4
  indexing-type-snd-fibered-Σ-Decomposition =
    indexing-type-Σ-Decomposition snd-fibered-Σ-Decomposition

  inhabited-cotype-snd-fibered-Σ-Decomposition :
    indexing-type-snd-fibered-Σ-Decomposition → Inhabited-Type l5
  inhabited-cotype-snd-fibered-Σ-Decomposition =
    inhabited-cotype-Σ-Decomposition snd-fibered-Σ-Decomposition

  cotype-snd-fibered-Σ-Decomposition :
    indexing-type-snd-fibered-Σ-Decomposition → UU l5
  cotype-snd-fibered-Σ-Decomposition =
    cotype-Σ-Decomposition snd-fibered-Σ-Decomposition

  matching-correspondence-snd-fibered-Σ-Decomposition :
    indexing-type-fst-fibered-Σ-Decomposition ≃
    Σ (indexing-type-Σ-Decomposition snd-fibered-Σ-Decomposition)
      (cotype-Σ-Decomposition snd-fibered-Σ-Decomposition)
  matching-correspondence-snd-fibered-Σ-Decomposition =
    matching-correspondence-Σ-Decomposition snd-fibered-Σ-Decomposition

  map-matching-correspondence-snd-fibered-Σ-Decomposition :
    indexing-type-fst-fibered-Σ-Decomposition →
    Σ (indexing-type-Σ-Decomposition snd-fibered-Σ-Decomposition)
      (cotype-Σ-Decomposition snd-fibered-Σ-Decomposition)
  map-matching-correspondence-snd-fibered-Σ-Decomposition =
    map-matching-correspondence-Σ-Decomposition
      snd-fibered-Σ-Decomposition
```

#### Displayed double Σ-decompositions

```agda
displayed-Σ-Decomposition :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : UU l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
displayed-Σ-Decomposition l2 l3 l4 l5 A =
  ( Σ (Σ-Decomposition l2 l3 A)
  ( λ D →
    (u : indexing-type-Σ-Decomposition D) →
    Σ-Decomposition l4 l5 (cotype-Σ-Decomposition D u)))

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : displayed-Σ-Decomposition l2 l3 l4 l5 A)
  where

  fst-displayed-Σ-Decomposition : Σ-Decomposition l2 l3 A
  fst-displayed-Σ-Decomposition = pr1 X

  indexing-type-fst-displayed-Σ-Decomposition : UU l2
  indexing-type-fst-displayed-Σ-Decomposition =
    indexing-type-Σ-Decomposition fst-displayed-Σ-Decomposition

  inhabited-cotype-fst-displayed-Σ-Decomposition :
    indexing-type-fst-displayed-Σ-Decomposition → Inhabited-Type l3
  inhabited-cotype-fst-displayed-Σ-Decomposition =
    inhabited-cotype-Σ-Decomposition fst-displayed-Σ-Decomposition

  cotype-fst-displayed-Σ-Decomposition :
    indexing-type-fst-displayed-Σ-Decomposition → UU l3
  cotype-fst-displayed-Σ-Decomposition =
    cotype-Σ-Decomposition fst-displayed-Σ-Decomposition

  matching-correspondence-fst-displayed-Σ-Decomposition :
    A ≃
    Σ (indexing-type-Σ-Decomposition fst-displayed-Σ-Decomposition)
      (cotype-Σ-Decomposition fst-displayed-Σ-Decomposition)
  matching-correspondence-fst-displayed-Σ-Decomposition =
    matching-correspondence-Σ-Decomposition
      fst-displayed-Σ-Decomposition

  map-matching-correspondence-fst-displayed-Σ-Decomposition :
    A →
    Σ (indexing-type-Σ-Decomposition fst-displayed-Σ-Decomposition)
      (cotype-Σ-Decomposition fst-displayed-Σ-Decomposition)
  map-matching-correspondence-fst-displayed-Σ-Decomposition =
    map-matching-correspondence-Σ-Decomposition
      fst-displayed-Σ-Decomposition

  snd-displayed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Σ-Decomposition) →
    Σ-Decomposition l4 l5 (cotype-fst-displayed-Σ-Decomposition x)
  snd-displayed-Σ-Decomposition = pr2 X

  indexing-type-snd-displayed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Σ-Decomposition) →
    UU l4
  indexing-type-snd-displayed-Σ-Decomposition x =
    indexing-type-Σ-Decomposition (snd-displayed-Σ-Decomposition x)

  inhabited-cotype-snd-displayed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Σ-Decomposition) →
    indexing-type-snd-displayed-Σ-Decomposition x → Inhabited-Type l5
  inhabited-cotype-snd-displayed-Σ-Decomposition x =
    inhabited-cotype-Σ-Decomposition (snd-displayed-Σ-Decomposition x)

  cotype-snd-displayed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Σ-Decomposition) →
    indexing-type-snd-displayed-Σ-Decomposition x →
    UU l5
  cotype-snd-displayed-Σ-Decomposition x =
    cotype-Σ-Decomposition (snd-displayed-Σ-Decomposition x)

  matching-correspondence-snd-displayed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Σ-Decomposition) →
    ( cotype-fst-displayed-Σ-Decomposition x ≃
      Σ ( indexing-type-snd-displayed-Σ-Decomposition x)
        ( cotype-snd-displayed-Σ-Decomposition x))
  matching-correspondence-snd-displayed-Σ-Decomposition x =
    matching-correspondence-Σ-Decomposition
      ( snd-displayed-Σ-Decomposition x)

  map-matching-correspondence-snd-displayed-Σ-Decomposition :
    ( x : indexing-type-fst-displayed-Σ-Decomposition) →
    cotype-fst-displayed-Σ-Decomposition x →
    Σ ( indexing-type-snd-displayed-Σ-Decomposition x)
      ( cotype-snd-displayed-Σ-Decomposition x)
  map-matching-correspondence-snd-displayed-Σ-Decomposition x =
    map-matching-correspondence-Σ-Decomposition
      ( snd-displayed-Σ-Decomposition x)
```

## Properties

### Characterization of equality of Σ-decompositions

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

  is-torsorial-equiv-Σ-Decomposition :
    is-torsorial (equiv-Σ-Decomposition X)
  is-torsorial-equiv-Σ-Decomposition =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (indexing-type-Σ-Decomposition X))
      ( pair (indexing-type-Σ-Decomposition X) id-equiv)
      ( is-torsorial-Eq-structure
        ( is-torsorial-equiv-Fam-Inhabited-Types
          ( inhabited-cotype-Σ-Decomposition X))
        ( pair
          ( inhabited-cotype-Σ-Decomposition X)
          ( id-equiv-Fam-Inhabited-Types (inhabited-cotype-Σ-Decomposition X)))
        ( is-torsorial-htpy-equiv
          ( matching-correspondence-Σ-Decomposition X)))

  equiv-eq-Σ-Decomposition :
    (Y : Σ-Decomposition l2 l3 A) → (X ＝ Y) → equiv-Σ-Decomposition X Y
  equiv-eq-Σ-Decomposition .X refl = id-equiv-Σ-Decomposition

  is-equiv-equiv-eq-Σ-Decomposition :
    (Y : Σ-Decomposition l2 l3 A) → is-equiv (equiv-eq-Σ-Decomposition Y)
  is-equiv-equiv-eq-Σ-Decomposition =
    fundamental-theorem-id
      is-torsorial-equiv-Σ-Decomposition
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

### Characterization of equality of set-indexed Σ-decompositions

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

  is-torsorial-equiv-Set-Indexed-Σ-Decomposition :
    is-torsorial (equiv-Set-Indexed-Σ-Decomposition X)
  is-torsorial-equiv-Set-Indexed-Σ-Decomposition =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv-Set (indexing-set-Set-Indexed-Σ-Decomposition X))
      ( pair (indexing-set-Set-Indexed-Σ-Decomposition X) id-equiv)
      ( is-torsorial-Eq-structure
        ( is-torsorial-equiv-Fam-Inhabited-Types
          ( inhabited-cotype-Set-Indexed-Σ-Decomposition X))
        ( pair
          ( inhabited-cotype-Set-Indexed-Σ-Decomposition X)
          ( id-equiv-Fam-Inhabited-Types
            ( inhabited-cotype-Set-Indexed-Σ-Decomposition X)))
        ( is-torsorial-htpy-equiv
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
      is-torsorial-equiv-Set-Indexed-Σ-Decomposition
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
  {A : UU l1} (X : fibered-Σ-Decomposition l2 l3 l4 l5 A)
  (Y : fibered-Σ-Decomposition l6 l7 l8 l9 A)
  where

  equiv-fst-fibered-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
  equiv-fst-fibered-Σ-Decomposition =
    equiv-Σ-Decomposition
    ( fst-fibered-Σ-Decomposition X)
    ( fst-fibered-Σ-Decomposition Y)

  equiv-snd-fibered-Σ-Decomposition :
    (e : equiv-fst-fibered-Σ-Decomposition) →
    UU (l4 ⊔ l5 ⊔ l6 ⊔ l8 ⊔ l9)
  equiv-snd-fibered-Σ-Decomposition e =
    equiv-Σ-Decomposition
      ( map-equiv-tr-Σ-Decomposition
        ( equiv-indexing-type-equiv-Σ-Decomposition
          ( fst-fibered-Σ-Decomposition X)
          ( fst-fibered-Σ-Decomposition Y)
          ( e))
        ( snd-fibered-Σ-Decomposition X))
      ( snd-fibered-Σ-Decomposition Y)

  equiv-fibered-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-fibered-Σ-Decomposition =
    Σ ( equiv-fst-fibered-Σ-Decomposition)
      ( equiv-snd-fibered-Σ-Decomposition)

  fst-equiv-fibered-Σ-Decomposition :
    (e : equiv-fibered-Σ-Decomposition) →
    equiv-fst-fibered-Σ-Decomposition
  fst-equiv-fibered-Σ-Decomposition = pr1

  snd-equiv-fibered-Σ-Decomposition :
    (e : equiv-fibered-Σ-Decomposition) →
    equiv-snd-fibered-Σ-Decomposition
      (fst-equiv-fibered-Σ-Decomposition e)
  snd-equiv-fibered-Σ-Decomposition = pr2

module _
  { l1 l2 l3 l4 l5 : Level} {A : UU l1}
  ( D : fibered-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = fst-fibered-Σ-Decomposition D
    Y = snd-fibered-Σ-Decomposition D

  is-torsorial-equiv-fibered-Σ-Decomposition :
    is-torsorial (equiv-fibered-Σ-Decomposition D)
  is-torsorial-equiv-fibered-Σ-Decomposition =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv-Σ-Decomposition X)
      ( X , id-equiv-Σ-Decomposition X)
      ( is-torsorial-Eq-structure
        ( is-torsorial-equiv (indexing-type-Σ-Decomposition Y))
        ( pair (indexing-type-Σ-Decomposition Y) id-equiv)
        ( is-torsorial-Eq-structure
          ( is-torsorial-equiv-Fam-Inhabited-Types
            ( inhabited-cotype-Σ-Decomposition Y))
          ( pair
            ( inhabited-cotype-Σ-Decomposition Y)
            ( id-equiv-Fam-Inhabited-Types
              ( inhabited-cotype-Σ-Decomposition Y)))
            ( is-torsorial-htpy-equiv
              ( matching-correspondence-Σ-Decomposition Y))))

  id-equiv-fibered-Σ-Decomposition :
    equiv-fibered-Σ-Decomposition D D
  pr1 id-equiv-fibered-Σ-Decomposition = id-equiv-Σ-Decomposition X
  pr1 (pr2 id-equiv-fibered-Σ-Decomposition) = id-equiv
  pr1 (pr2 (pr2 id-equiv-fibered-Σ-Decomposition)) x = id-equiv
  pr2 (pr2 (pr2 id-equiv-fibered-Σ-Decomposition)) = refl-htpy

  equiv-eq-fibered-Σ-Decomposition :
    (D' : fibered-Σ-Decomposition l2 l3 l4 l5 A) →
    (D ＝ D') → equiv-fibered-Σ-Decomposition D D'
  equiv-eq-fibered-Σ-Decomposition .D refl =
    id-equiv-fibered-Σ-Decomposition

  is-equiv-equiv-eq-fibered-Σ-Decomposition :
    (D' : fibered-Σ-Decomposition l2 l3 l4 l5 A) →
    is-equiv (equiv-eq-fibered-Σ-Decomposition D')
  is-equiv-equiv-eq-fibered-Σ-Decomposition =
    fundamental-theorem-id
      is-torsorial-equiv-fibered-Σ-Decomposition
      equiv-eq-fibered-Σ-Decomposition

  extensionality-fibered-Σ-Decomposition :
    (D' : fibered-Σ-Decomposition l2 l3 l4 l5 A) →
    (D ＝ D') ≃ equiv-fibered-Σ-Decomposition D D'
  pr1 (extensionality-fibered-Σ-Decomposition D') =
    equiv-eq-fibered-Σ-Decomposition D'
  pr2 (extensionality-fibered-Σ-Decomposition D') =
    is-equiv-equiv-eq-fibered-Σ-Decomposition D'

  eq-equiv-fibered-Σ-Decomposition :
    (D' : fibered-Σ-Decomposition l2 l3 l4 l5 A) →
    (equiv-fibered-Σ-Decomposition D D') → (D ＝ D')
  eq-equiv-fibered-Σ-Decomposition D' =
    map-inv-equiv (extensionality-fibered-Σ-Decomposition D')
```

#### Characterization of identity type for displayed double Σ-decompositions

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (X : displayed-Σ-Decomposition l2 l3 l4 l5 A)
  (Y : displayed-Σ-Decomposition l6 l7 l8 l9 A)
  where

  equiv-fst-displayed-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
  equiv-fst-displayed-Σ-Decomposition =
    equiv-Σ-Decomposition
    ( fst-displayed-Σ-Decomposition X)
    ( fst-displayed-Σ-Decomposition Y)

  equiv-snd-displayed-Σ-Decomposition :
    (e : equiv-fst-displayed-Σ-Decomposition) →
    UU (l2 ⊔ l4 ⊔ l5 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-snd-displayed-Σ-Decomposition e =
    ( x : indexing-type-fst-displayed-Σ-Decomposition X) →
    equiv-Σ-Decomposition
      ( map-equiv-tr-Σ-Decomposition
        ( equiv-cotype-equiv-Σ-Decomposition
          ( fst-displayed-Σ-Decomposition X)
          ( fst-displayed-Σ-Decomposition Y)
          ( e)
          ( x))
        ( snd-displayed-Σ-Decomposition X x))
      ( snd-displayed-Σ-Decomposition Y
        ( map-equiv-indexing-type-equiv-Σ-Decomposition
          ( fst-displayed-Σ-Decomposition X)
          ( fst-displayed-Σ-Decomposition Y)
          ( e)
          ( x)))

  equiv-displayed-Σ-Decomposition :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
  equiv-displayed-Σ-Decomposition =
    Σ ( equiv-fst-displayed-Σ-Decomposition)
      ( equiv-snd-displayed-Σ-Decomposition)

  fst-equiv-displayed-Σ-Decomposition :
    (e : equiv-displayed-Σ-Decomposition) →
    equiv-fst-displayed-Σ-Decomposition
  fst-equiv-displayed-Σ-Decomposition = pr1

  snd-equiv-displayed-Σ-Decomposition :
    (e : equiv-displayed-Σ-Decomposition) →
    equiv-snd-displayed-Σ-Decomposition
      ( fst-equiv-displayed-Σ-Decomposition e)
  snd-equiv-displayed-Σ-Decomposition = pr2

module _
  { l1 l2 l3 l4 l5 : Level} {A : UU l1}
  ( disp-D : displayed-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = fst-displayed-Σ-Decomposition disp-D
    f-Y = snd-displayed-Σ-Decomposition disp-D

  is-torsorial-equiv-displayed-Σ-Decomposition :
    is-torsorial (equiv-displayed-Σ-Decomposition disp-D)
  is-torsorial-equiv-displayed-Σ-Decomposition =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv-Σ-Decomposition X)
      ( pair X (id-equiv-Σ-Decomposition X))
      ( is-contr-equiv
        ( Π-total-fam (λ x → _))
        ( inv-distributive-Π-Σ)
        ( is-contr-Π (λ x → is-torsorial-equiv-Σ-Decomposition (f-Y x))))

  id-equiv-displayed-Σ-Decomposition :
    equiv-displayed-Σ-Decomposition disp-D disp-D
  pr1 id-equiv-displayed-Σ-Decomposition = id-equiv-Σ-Decomposition X
  pr1 (pr2 id-equiv-displayed-Σ-Decomposition x) = id-equiv
  pr1 (pr2 (pr2 id-equiv-displayed-Σ-Decomposition x)) y = id-equiv
  pr2 (pr2 (pr2 id-equiv-displayed-Σ-Decomposition x)) = refl-htpy

  equiv-eq-displayed-Σ-Decomposition :
    (disp-D' : displayed-Σ-Decomposition l2 l3 l4 l5 A) →
    (disp-D ＝ disp-D') → equiv-displayed-Σ-Decomposition disp-D disp-D'
  equiv-eq-displayed-Σ-Decomposition .disp-D refl =
    id-equiv-displayed-Σ-Decomposition

  is-equiv-equiv-eq-displayed-Σ-Decomposition :
    (disp-D' : displayed-Σ-Decomposition l2 l3 l4 l5 A) →
    is-equiv (equiv-eq-displayed-Σ-Decomposition disp-D')
  is-equiv-equiv-eq-displayed-Σ-Decomposition =
    fundamental-theorem-id
      is-torsorial-equiv-displayed-Σ-Decomposition
      equiv-eq-displayed-Σ-Decomposition

  extensionality-displayed-Σ-Decomposition :
    (disp-D' : displayed-Σ-Decomposition l2 l3 l4 l5 A) →
    (disp-D ＝ disp-D') ≃ equiv-displayed-Σ-Decomposition disp-D disp-D'
  pr1 (extensionality-displayed-Σ-Decomposition D) =
    equiv-eq-displayed-Σ-Decomposition D
  pr2 (extensionality-displayed-Σ-Decomposition D) =
    is-equiv-equiv-eq-displayed-Σ-Decomposition D

  eq-equiv-displayed-Σ-Decomposition :
    (disp-D' : displayed-Σ-Decomposition l2 l3 l4 l5 A) →
    (equiv-displayed-Σ-Decomposition disp-D disp-D') → (disp-D ＝ disp-D')
  eq-equiv-displayed-Σ-Decomposition D =
    map-inv-equiv
      (extensionality-displayed-Σ-Decomposition D)
```

#### Equivalence between fibered double Σ-decompositions and displayed double Σ-decompositions

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (fib-D : fibered-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    X = indexing-type-fst-fibered-Σ-Decomposition fib-D
    Y = cotype-fst-fibered-Σ-Decomposition fib-D
    Y-Inhabited-Type = inhabited-cotype-fst-fibered-Σ-Decomposition fib-D
    e = matching-correspondence-Σ-Decomposition
      ( fst-fibered-Σ-Decomposition fib-D)
    U = indexing-type-snd-fibered-Σ-Decomposition fib-D
    V = cotype-snd-fibered-Σ-Decomposition fib-D
    V-Inhabited-Type = inhabited-cotype-snd-fibered-Σ-Decomposition fib-D
    f = matching-correspondence-Σ-Decomposition
      ( snd-fibered-Σ-Decomposition fib-D)

  matching-correspondence-displayed-fibered-Σ-Decomposition :
    A ≃ Σ U (λ u → Σ (V u) (λ v → Y (map-inv-equiv f (u , v))))
  matching-correspondence-displayed-fibered-Σ-Decomposition =
    equivalence-reasoning
    A ≃ Σ X Y by e
      ≃ Σ ( Σ U V) (λ uv → Y ((map-inv-equiv f) uv))
        by inv-equiv ( equiv-Σ-equiv-base Y (inv-equiv f))
      ≃ Σ U ( λ u → Σ (V u) (λ v → Y (map-inv-equiv f (u , v))))
        by associative-Σ

  map-displayed-fibered-Σ-Decomposition :
    displayed-Σ-Decomposition l4 (l3 ⊔ l5) l5 l3 A
  pr1 (pr1 map-displayed-fibered-Σ-Decomposition) = U
  pr1 (pr2 (pr1 map-displayed-fibered-Σ-Decomposition)) u =
    Σ-Inhabited-Type
      ( V-Inhabited-Type u)
      ( λ v → Y-Inhabited-Type (map-inv-equiv f (u , v)))
  pr2 (pr2 (pr1 map-displayed-fibered-Σ-Decomposition)) =
    matching-correspondence-displayed-fibered-Σ-Decomposition
  pr1 (pr2 map-displayed-fibered-Σ-Decomposition u) = V u
  pr1 (pr2 (pr2 map-displayed-fibered-Σ-Decomposition u)) v =
    Y-Inhabited-Type (map-inv-equiv f (u , v))
  pr2 (pr2 (pr2 map-displayed-fibered-Σ-Decomposition u)) = id-equiv

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (disp-D : displayed-Σ-Decomposition l2 l3 l4 l5 A)
  where

  private
    M = indexing-type-fst-displayed-Σ-Decomposition disp-D
    N = cotype-fst-displayed-Σ-Decomposition disp-D
    s = matching-correspondence-Σ-Decomposition
      ( fst-displayed-Σ-Decomposition disp-D)
    P = indexing-type-snd-displayed-Σ-Decomposition disp-D
    Q-Inhabited-Type =
      inhabited-cotype-snd-displayed-Σ-Decomposition disp-D
    Q = cotype-snd-displayed-Σ-Decomposition disp-D
    t = matching-correspondence-snd-displayed-Σ-Decomposition disp-D

  matching-correspondence-inv-displayed-fibered-Σ-Decomposition :
    A ≃ Σ (Σ M P) (λ (m , p) → Q m p)
  matching-correspondence-inv-displayed-fibered-Σ-Decomposition =
    equivalence-reasoning
    A ≃ Σ M N by s
      ≃ Σ M (λ m → Σ (P m) (Q m))
      by equiv-Σ (λ m → Σ (P m) (Q m)) id-equiv t
      ≃ Σ (Σ M P) (λ (m , p) → Q m p)
      by inv-associative-Σ

  map-inv-displayed-fibered-Σ-Decomposition :
    fibered-Σ-Decomposition (l2 ⊔ l4) l5 l2 l4 A
  pr1 (pr1 map-inv-displayed-fibered-Σ-Decomposition) = Σ M P
  pr1 (pr2 (pr1 map-inv-displayed-fibered-Σ-Decomposition)) (m , p) =
    Q-Inhabited-Type m p
  pr2 (pr2 (pr1 map-inv-displayed-fibered-Σ-Decomposition)) =
    matching-correspondence-inv-displayed-fibered-Σ-Decomposition
  pr1 (pr2 map-inv-displayed-fibered-Σ-Decomposition) = M
  pr1 (pr1 (pr2 (pr2 map-inv-displayed-fibered-Σ-Decomposition)) m) = P m
  pr2 (pr1 (pr2 (pr2 map-inv-displayed-fibered-Σ-Decomposition)) m) =
    ind-trunc-Prop
      ( λ n → trunc-Prop (P m))
      ( λ n → unit-trunc-Prop (pr1 (map-equiv (t m) n)))
      ( is-inhabited-cotype-Σ-Decomposition
        ( fst-displayed-Σ-Decomposition disp-D)
        ( m))
  pr2 (pr2 (pr2 map-inv-displayed-fibered-Σ-Decomposition)) = id-equiv

module _
  {l1 l : Level} {A : UU l1}
  (fib-D : fibered-Σ-Decomposition l l l l A)
  where

  private
    X = indexing-type-fst-fibered-Σ-Decomposition fib-D
    Y = cotype-fst-fibered-Σ-Decomposition fib-D
    e = matching-correspondence-Σ-Decomposition
      ( fst-fibered-Σ-Decomposition fib-D)
    U = indexing-type-snd-fibered-Σ-Decomposition fib-D
    V = cotype-snd-fibered-Σ-Decomposition fib-D
    f = matching-correspondence-Σ-Decomposition
      ( snd-fibered-Σ-Decomposition fib-D)
    disp-D = map-displayed-fibered-Σ-Decomposition fib-D
    M = indexing-type-fst-displayed-Σ-Decomposition disp-D
    N = cotype-fst-displayed-Σ-Decomposition disp-D
    s = matching-correspondence-Σ-Decomposition
      ( fst-displayed-Σ-Decomposition disp-D)
    P = indexing-type-snd-displayed-Σ-Decomposition disp-D
    Q = cotype-snd-displayed-Σ-Decomposition disp-D
    t = matching-correspondence-snd-displayed-Σ-Decomposition disp-D

    htpy-matching-correspondence :
      ( map-equiv
        ( ( equiv-Σ Y (inv-equiv f) (λ (m , p) → id-equiv)) ∘e
          ( matching-correspondence-inv-displayed-fibered-Σ-Decomposition
            ( disp-D)))) ~
      ( map-equiv e)
    htpy-matching-correspondence a =
      htpy-eq-equiv
        ( right-inverse-law-equiv (equiv-Σ-equiv-base Y (inv-equiv f)))
        ( map-equiv e a)

  is-retraction-map-inv-displayed-fibered-Σ-Decomposition :
    map-inv-displayed-fibered-Σ-Decomposition
      ( map-displayed-fibered-Σ-Decomposition fib-D) ＝ fib-D
  is-retraction-map-inv-displayed-fibered-Σ-Decomposition =
    eq-equiv-fibered-Σ-Decomposition
      ( map-inv-displayed-fibered-Σ-Decomposition
        ( map-displayed-fibered-Σ-Decomposition fib-D))
      ( fib-D)
      ( ( ( inv-equiv f) ,
          ( ( λ x → id-equiv) ,
            ( htpy-matching-correspondence))) ,
        ( ( id-equiv) ,
          ( ( λ u → id-equiv) ,
            ( λ a → refl))))

module _
  {l1 l : Level} {A : UU l1}
  (disp-D : displayed-Σ-Decomposition l l l l A)
  where

  private
    M = indexing-type-fst-displayed-Σ-Decomposition disp-D
    N = cotype-fst-displayed-Σ-Decomposition disp-D
    s = matching-correspondence-Σ-Decomposition
      ( fst-displayed-Σ-Decomposition disp-D)
    P = indexing-type-snd-displayed-Σ-Decomposition disp-D
    Q = cotype-snd-displayed-Σ-Decomposition disp-D
    t = matching-correspondence-snd-displayed-Σ-Decomposition disp-D
    fib-D = map-inv-displayed-fibered-Σ-Decomposition disp-D
    X = indexing-type-fst-fibered-Σ-Decomposition fib-D
    Y = cotype-fst-fibered-Σ-Decomposition fib-D
    e = matching-correspondence-Σ-Decomposition
      ( fst-fibered-Σ-Decomposition fib-D)
    U = indexing-type-snd-fibered-Σ-Decomposition fib-D
    V = cotype-snd-fibered-Σ-Decomposition fib-D
    f = matching-correspondence-Σ-Decomposition
      ( snd-fibered-Σ-Decomposition fib-D)

    htpy-matching-correspondence :
      map-equiv
        ( equiv-Σ N id-equiv (inv-equiv ∘ t) ∘e
          matching-correspondence-displayed-fibered-Σ-Decomposition
            (fib-D)) ~
      map-equiv s
    htpy-matching-correspondence x =
      ( ap
        ( λ f → map-equiv (equiv-tot (inv-equiv ∘ t)) f)
        ( map-inv-eq-transpose-equiv
          ( associative-Σ)
          ( inv
            ( map-eq-transpose-equiv
              ( equiv-Σ-equiv-base Y (inv-equiv id-equiv))
              ( inv
                ( map-eq-transpose-equiv
                  ( associative-Σ)
                  ( is-section-map-inv-associative-Σ
                    ( map-equiv (equiv-tot t ∘e s) x)))))))) ∙
      ( inv
        ( preserves-comp-tot
          ( map-equiv ∘ t)
          ( map-inv-equiv ∘ t)
          ( map-equiv s x)) ∙
      ( tot-htpy (λ z → is-retraction-map-inv-equiv (t z)) (map-equiv s x) ∙
      ( tot-id
        ( λ z → cotype-fst-displayed-Σ-Decomposition disp-D z)
        ( map-equiv s x))))

  is-section-map-inv-displayed-fibered-Σ-Decomposition :
    ( map-displayed-fibered-Σ-Decomposition
      {l1} {l} {l} {l} {l} {A} fib-D) ＝
    disp-D
  is-section-map-inv-displayed-fibered-Σ-Decomposition =
    eq-equiv-displayed-Σ-Decomposition
      ( map-displayed-fibered-Σ-Decomposition fib-D)
      ( disp-D)
      ( ( ( id-equiv) ,
          ( ( inv-equiv ∘ t) ,
            ( htpy-matching-correspondence))) ,
        ( λ (m : M) →
          ( ( id-equiv) ,
            ( ( λ (p : P m) → id-equiv) ,
              ( refl-htpy)))))

is-equiv-map-displayed-fibered-Σ-Decomposition :
  {l1 l : Level} → {A : UU l1} →
  is-equiv
    ( map-displayed-fibered-Σ-Decomposition {l1} {l} {l} {l} {l} {A})
is-equiv-map-displayed-fibered-Σ-Decomposition =
  is-equiv-is-invertible
    ( map-inv-displayed-fibered-Σ-Decomposition)
    ( is-section-map-inv-displayed-fibered-Σ-Decomposition)
    ( is-retraction-map-inv-displayed-fibered-Σ-Decomposition)

equiv-displayed-fibered-Σ-Decomposition :
  {l1 l : Level} → {A : UU l1} →
  fibered-Σ-Decomposition l l l l A ≃
  displayed-Σ-Decomposition l l l l A
pr1 equiv-displayed-fibered-Σ-Decomposition =
  map-displayed-fibered-Σ-Decomposition
pr2 equiv-displayed-fibered-Σ-Decomposition =
  is-equiv-map-displayed-fibered-Σ-Decomposition
```
