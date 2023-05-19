# Π-decompositions of types

```agda
{-# OPTIONS --lossy-unification #-}
module foundation.pi-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence

open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.functions
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.type-arithmetic-dependent-pair-types
open import foundation-core.universe-levels
```

</details>

## Idea

A Π-decomposition of a type `A` consists of a type `X` and a family of inhabited
types `Y x` indexed by `x : X` equipped with an equivalence `A ≃ Π X Y`. The
type `X` is called the indexing type of the Π-decomposition, the elements of
`Y x` are called the cotypes of the Π-decomposition, and the equivalence
`A ≃ Π X Y` is the matching correspondence of the Π-decomposition

## Definitions

### General Π-decompositions

```agda
Π-Decomposition :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Π-Decomposition l2 l3 A =
  Σ ( UU l2)
    ( λ X →
      Σ ( Fam-Inhabited-Types l3 X)
        ( λ Y → A ≃ ((x : X) → type-Inhabited-Type (Y x))))

module _
  {l1 l2 l3 : Level} {A : UU l1} (D : Π-Decomposition l2 l3 A)
  where

  indexing-type-Π-Decomposition : UU l2
  indexing-type-Π-Decomposition = pr1 D

  inhabited-cotype-Π-Decomposition :
    Fam-Inhabited-Types l3 indexing-type-Π-Decomposition
  inhabited-cotype-Π-Decomposition = pr1 (pr2 D)

  cotype-Π-Decomposition : indexing-type-Π-Decomposition → UU l3
  cotype-Π-Decomposition =
    type-Fam-Inhabited-Types inhabited-cotype-Π-Decomposition

  is-inhabited-cotype-Π-Decomposition :
    (x : indexing-type-Π-Decomposition) →
    is-inhabited (cotype-Π-Decomposition x)
  is-inhabited-cotype-Π-Decomposition x =
    is-inhabited-type-Inhabited-Type (inhabited-cotype-Π-Decomposition x)

  matching-correspondence-Π-Decomposition :
    A ≃ ((x : indexing-type-Π-Decomposition) → cotype-Π-Decomposition x)
  matching-correspondence-Π-Decomposition = pr2 (pr2 D)

  map-matching-correspondence-Π-Decomposition :
    A → ((x : indexing-type-Π-Decomposition) → cotype-Π-Decomposition x)
  map-matching-correspondence-Π-Decomposition =
    map-equiv matching-correspondence-Π-Decomposition

  is-inhabited-indexing-type-inhabited-Π-Decomposition :
    (p : is-inhabited A) → (is-inhabited (indexing-type-Π-Decomposition))
  is-inhabited-indexing-type-inhabited-Π-Decomposition p =
    {!!}

  inhabited-indexing-type-inhabited-Π-Decomposition :
    (p : is-inhabited A) → (Inhabited-Type l2)
  pr1 (inhabited-indexing-type-inhabited-Π-Decomposition p) =
    indexing-type-Π-Decomposition
  pr2 (inhabited-indexing-type-inhabited-Π-Decomposition p) =
    is-inhabited-indexing-type-inhabited-Π-Decomposition p

  is-inhabited-base-is-inhabited-indexing-type-Π-Decomposition :
    (is-inhabited (indexing-type-Π-Decomposition)) → (is-inhabited A)
  is-inhabited-base-is-inhabited-indexing-type-Π-Decomposition p =
    {!!}
```

### Set-indexed Π-decompositions

```agda
Set-Indexed-Π-Decomposition :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Set-Indexed-Π-Decomposition l2 l3 A =
  Σ ( Set l2)
    ( λ X →
      Σ ( Fam-Inhabited-Types l3 (type-Set X))
        ( λ Y → A ≃ total-Fam-Inhabited-Types Y))

module _
  {l1 l2 l3 : Level} {A : UU l1} (D : Set-Indexed-Π-Decomposition l2 l3 A)
  where

  indexing-set-Set-Indexed-Π-Decomposition : Set l2
  indexing-set-Set-Indexed-Π-Decomposition = pr1 D

  indexing-type-Set-Indexed-Π-Decomposition : UU l2
  indexing-type-Set-Indexed-Π-Decomposition =
    type-Set indexing-set-Set-Indexed-Π-Decomposition

  inhabited-cotype-Set-Indexed-Π-Decomposition :
    indexing-type-Set-Indexed-Π-Decomposition → Inhabited-Type l3
  inhabited-cotype-Set-Indexed-Π-Decomposition = pr1 (pr2 D)

  cotype-Set-Indexed-Π-Decomposition :
    indexing-type-Set-Indexed-Π-Decomposition → UU l3
  cotype-Set-Indexed-Π-Decomposition x =
    type-Inhabited-Type (inhabited-cotype-Set-Indexed-Π-Decomposition x)

  is-inhabited-cotype-Set-Indexed-Π-Decomposition :
    (x : indexing-type-Set-Indexed-Π-Decomposition) →
    is-inhabited (cotype-Set-Indexed-Π-Decomposition x)
  is-inhabited-cotype-Set-Indexed-Π-Decomposition x =
    is-inhabited-type-Inhabited-Type
      ( inhabited-cotype-Set-Indexed-Π-Decomposition x)

  matching-correspondence-Set-Indexed-Π-Decomposition :
    A ≃
    Σ indexing-type-Set-Indexed-Π-Decomposition
      cotype-Set-Indexed-Π-Decomposition
  matching-correspondence-Set-Indexed-Π-Decomposition = pr2 (pr2 D)

  map-matching-correspondence-Set-Indexed-Π-Decomposition :
    A →
    Σ indexing-type-Set-Indexed-Π-Decomposition
      cotype-Set-Indexed-Π-Decomposition
  map-matching-correspondence-Set-Indexed-Π-Decomposition =
    map-equiv matching-correspondence-Set-Indexed-Π-Decomposition

  index-Set-Indexed-Π-Decomposition :
    A → indexing-type-Set-Indexed-Π-Decomposition
  index-Set-Indexed-Π-Decomposition a =
    pr1 (map-matching-correspondence-Set-Indexed-Π-Decomposition a)
```

### Fibered double Π-decompositions

```agda
fibered-Π-Decomposition :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : UU l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
fibered-Π-Decomposition l2 l3 l4 l5 A =
  Σ (Π-Decomposition l2 l3 A)
    ( λ D → Π-Decomposition l4 l5 (indexing-type-Π-Decomposition D))

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : fibered-Π-Decomposition l2 l3 l4 l5 A)
  where

  fst-fibered-Π-Decomposition : Π-Decomposition l2 l3 A
  fst-fibered-Π-Decomposition = pr1 X

  indexing-type-fst-fibered-Π-Decomposition : UU l2
  indexing-type-fst-fibered-Π-Decomposition =
    indexing-type-Π-Decomposition fst-fibered-Π-Decomposition

  inhabited-cotype-fst-fibered-Π-Decomposition :
    indexing-type-fst-fibered-Π-Decomposition → Inhabited-Type l3
  inhabited-cotype-fst-fibered-Π-Decomposition =
    inhabited-cotype-Π-Decomposition fst-fibered-Π-Decomposition

  cotype-fst-fibered-Π-Decomposition :
    indexing-type-fst-fibered-Π-Decomposition → UU l3
  cotype-fst-fibered-Π-Decomposition =
    cotype-Π-Decomposition fst-fibered-Π-Decomposition

  matching-correspondence-fst-fibered-Π-Decomposition :
    A ≃
    ( (x : indexing-type-Π-Decomposition fst-fibered-Π-Decomposition) →
      (cotype-Π-Decomposition fst-fibered-Π-Decomposition x))
  matching-correspondence-fst-fibered-Π-Decomposition =
    matching-correspondence-Π-Decomposition fst-fibered-Π-Decomposition

  map-matching-correspondence-fst-fibered-Π-Decomposition :
    A →
    ( (x : indexing-type-Π-Decomposition fst-fibered-Π-Decomposition) →
      (cotype-Π-Decomposition fst-fibered-Π-Decomposition x))
  map-matching-correspondence-fst-fibered-Π-Decomposition =
    map-matching-correspondence-Π-Decomposition
      fst-fibered-Π-Decomposition

  snd-fibered-Π-Decomposition :
      Π-Decomposition l4 l5 indexing-type-fst-fibered-Π-Decomposition
  snd-fibered-Π-Decomposition = pr2 X

  indexing-type-snd-fibered-Π-Decomposition : UU l4
  indexing-type-snd-fibered-Π-Decomposition =
    indexing-type-Π-Decomposition snd-fibered-Π-Decomposition

  inhabited-cotype-snd-fibered-Π-Decomposition :
    indexing-type-snd-fibered-Π-Decomposition → Inhabited-Type l5
  inhabited-cotype-snd-fibered-Π-Decomposition =
    inhabited-cotype-Π-Decomposition snd-fibered-Π-Decomposition

  cotype-snd-fibered-Π-Decomposition :
    indexing-type-snd-fibered-Π-Decomposition → UU l5
  cotype-snd-fibered-Π-Decomposition =
    cotype-Π-Decomposition snd-fibered-Π-Decomposition

  matching-correspondence-snd-fibered-Π-Decomposition :
    indexing-type-fst-fibered-Π-Decomposition ≃
    ( ( x : indexing-type-Π-Decomposition snd-fibered-Π-Decomposition) →
      (cotype-Π-Decomposition snd-fibered-Π-Decomposition x))
  matching-correspondence-snd-fibered-Π-Decomposition =
    matching-correspondence-Π-Decomposition snd-fibered-Π-Decomposition

  map-matching-correspondence-snd-fibered-Π-Decomposition :
    indexing-type-fst-fibered-Π-Decomposition →
    ( (x : indexing-type-Π-Decomposition snd-fibered-Π-Decomposition) →
      (cotype-Π-Decomposition snd-fibered-Π-Decomposition x))
  map-matching-correspondence-snd-fibered-Π-Decomposition =
    map-matching-correspondence-Π-Decomposition
      snd-fibered-Π-Decomposition
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

  inhabited-cotype-fst-displayed-Π-Decomposition :
    indexing-type-fst-displayed-Π-Decomposition → Inhabited-Type l3
  inhabited-cotype-fst-displayed-Π-Decomposition =
    inhabited-cotype-Π-Decomposition fst-displayed-Π-Decomposition

  cotype-fst-displayed-Π-Decomposition :
    indexing-type-fst-displayed-Π-Decomposition → UU l3
  cotype-fst-displayed-Π-Decomposition =
    cotype-Π-Decomposition fst-displayed-Π-Decomposition

  matching-correspondence-fst-displayed-Π-Decomposition :
    A ≃
    ( (x : indexing-type-Π-Decomposition fst-displayed-Π-Decomposition) →
      (cotype-Π-Decomposition fst-displayed-Π-Decomposition x))
  matching-correspondence-fst-displayed-Π-Decomposition =
    matching-correspondence-Π-Decomposition
      fst-displayed-Π-Decomposition

  map-matching-correspondence-fst-displayed-Π-Decomposition :
    A →
    ( (x : indexing-type-Π-Decomposition fst-displayed-Π-Decomposition) →
      (cotype-Π-Decomposition fst-displayed-Π-Decomposition x))
  map-matching-correspondence-fst-displayed-Π-Decomposition =
    map-matching-correspondence-Π-Decomposition
      fst-displayed-Π-Decomposition

  snd-displayed-Π-Decomposition :
    ( x : indexing-type-fst-displayed-Π-Decomposition) →
    Π-Decomposition l4 l5 (cotype-fst-displayed-Π-Decomposition x)
  snd-displayed-Π-Decomposition = pr2 X

  indexing-type-snd-displayed-Π-Decomposition :
    ( x : indexing-type-fst-displayed-Π-Decomposition) →
    UU l4
  indexing-type-snd-displayed-Π-Decomposition x =
    indexing-type-Π-Decomposition (snd-displayed-Π-Decomposition x)

  inhabited-cotype-snd-displayed-Π-Decomposition :
    ( x : indexing-type-fst-displayed-Π-Decomposition) →
    indexing-type-snd-displayed-Π-Decomposition x → Inhabited-Type l5
  inhabited-cotype-snd-displayed-Π-Decomposition x =
    inhabited-cotype-Π-Decomposition (snd-displayed-Π-Decomposition x)

  cotype-snd-displayed-Π-Decomposition :
    ( x : indexing-type-fst-displayed-Π-Decomposition) →
    indexing-type-snd-displayed-Π-Decomposition x →
    UU l5
  cotype-snd-displayed-Π-Decomposition x =
    cotype-Π-Decomposition (snd-displayed-Π-Decomposition x)

  matching-correspondence-snd-displayed-Π-Decomposition :
    ( x : indexing-type-fst-displayed-Π-Decomposition) →
    ( cotype-fst-displayed-Π-Decomposition x ≃
      ( (y : indexing-type-snd-displayed-Π-Decomposition x) →
        ( cotype-snd-displayed-Π-Decomposition x y)))
  matching-correspondence-snd-displayed-Π-Decomposition x =
    matching-correspondence-Π-Decomposition
      ( snd-displayed-Π-Decomposition x)

  map-matching-correspondence-snd-displayed-Π-Decomposition :
    ( x : indexing-type-fst-displayed-Π-Decomposition) →
    cotype-fst-displayed-Π-Decomposition x →
    ( (y : indexing-type-snd-displayed-Π-Decomposition x) →
      ( cotype-snd-displayed-Π-Decomposition x y))
  map-matching-correspondence-snd-displayed-Π-Decomposition x =
    map-matching-correspondence-Π-Decomposition
      ( snd-displayed-Π-Decomposition x)
```

## Properties

### Characterization of equality of Π-Decompositions

```agda
equiv-Π-Decomposition :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : Π-Decomposition l2 l3 A) (Y : Π-Decomposition l4 l5 A) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
equiv-Π-Decomposition X Y =
  Σ ( indexing-type-Π-Decomposition X ≃ indexing-type-Π-Decomposition Y)
    ( λ e →
      Σ ( (x : indexing-type-Π-Decomposition X) →
          cotype-Π-Decomposition X x ≃ cotype-Π-Decomposition Y (map-equiv e x))
        ( λ f → {!!}))

-- module _
--   {l1 l2 l3 l4 l5 : Level} {A : UU l1}
--   (X : Π-Decomposition l2 l3 A) (Y : Π-Decomposition l4 l5 A)
--   (e : equiv-Π-Decomposition X Y)
--   where

--   equiv-indexing-type-equiv-Π-Decomposition :
--     indexing-type-Π-Decomposition X ≃ indexing-type-Π-Decomposition Y
--   equiv-indexing-type-equiv-Π-Decomposition = pr1 e

--   map-equiv-indexing-type-equiv-Π-Decomposition :
--     indexing-type-Π-Decomposition X → indexing-type-Π-Decomposition Y
--   map-equiv-indexing-type-equiv-Π-Decomposition =
--     map-equiv equiv-indexing-type-equiv-Π-Decomposition

--   equiv-cotype-equiv-Π-Decomposition :
--     (x : indexing-type-Π-Decomposition X) →
--     cotype-Π-Decomposition X x ≃
--     cotype-Π-Decomposition Y (map-equiv-indexing-type-equiv-Π-Decomposition x)
--   equiv-cotype-equiv-Π-Decomposition = pr1 (pr2 e)

--   map-equiv-cotype-equiv-Π-Decomposition :
--     (x : indexing-type-Π-Decomposition X) →
--     cotype-Π-Decomposition X x →
--     cotype-Π-Decomposition Y (map-equiv-indexing-type-equiv-Π-Decomposition x)
--   map-equiv-cotype-equiv-Π-Decomposition x =
--     map-equiv (equiv-cotype-equiv-Π-Decomposition x)

-- module _
--   {l1 l2 l3 : Level} {A : UU l1} (X : Π-Decomposition l2 l3 A)
--   where

--   id-equiv-Π-Decomposition : equiv-Π-Decomposition X X
--   pr1 id-equiv-Π-Decomposition = id-equiv
--   pr1 (pr2 id-equiv-Π-Decomposition) x = id-equiv
--   pr2 (pr2 id-equiv-Π-Decomposition) = refl-htpy

--   is-contr-total-equiv-Π-Decomposition :
--     is-contr (Σ (Π-Decomposition l2 l3 A) (equiv-Π-Decomposition X))
--   is-contr-total-equiv-Π-Decomposition =
--     is-contr-total-Eq-structure
--       ( λ U Vf e →
--         Σ ( (x : indexing-type-Π-Decomposition X) →
--             cotype-Π-Decomposition X x ≃
--             type-Inhabited-Type (pr1 Vf (map-equiv e x)))
--           ( λ f →
--             ( ( map-equiv
--                 ( equiv-Σ (λ u → type-Inhabited-Type (pr1 Vf u)) e f)) ∘
--               ( map-matching-correspondence-Π-Decomposition X)) ~
--             ( map-equiv (pr2 Vf))))
--       ( is-contr-total-equiv (indexing-type-Π-Decomposition X))
--       ( pair (indexing-type-Π-Decomposition X) id-equiv)
--       ( is-contr-total-Eq-structure
--         ( λ V g f →
--           ( ( map-equiv
--               ( equiv-Σ (λ y → type-Inhabited-Type (V y)) id-equiv f)) ∘
--             ( map-matching-correspondence-Π-Decomposition X)) ~
--           ( map-equiv g))
--         ( is-contr-total-equiv-Fam-Inhabited-Types
--           ( inhabited-cotype-Π-Decomposition X))
--         ( pair
--           ( inhabited-cotype-Π-Decomposition X)
--           ( id-equiv-Fam-Inhabited-Types (inhabited-cotype-Π-Decomposition X)))
--         ( is-contr-total-htpy-equiv
--           ( matching-correspondence-Π-Decomposition X)))

--   equiv-eq-Π-Decomposition :
--     (Y : Π-Decomposition l2 l3 A) → (X ＝ Y) → equiv-Π-Decomposition X Y
--   equiv-eq-Π-Decomposition .X refl = id-equiv-Π-Decomposition

--   is-equiv-equiv-eq-Π-Decomposition :
--     (Y : Π-Decomposition l2 l3 A) → is-equiv (equiv-eq-Π-Decomposition Y)
--   is-equiv-equiv-eq-Π-Decomposition =
--     fundamental-theorem-id
--       is-contr-total-equiv-Π-Decomposition
--       equiv-eq-Π-Decomposition

--   extensionality-Π-Decomposition :
--     (Y : Π-Decomposition l2 l3 A) → (X ＝ Y) ≃ equiv-Π-Decomposition X Y
--   pr1 (extensionality-Π-Decomposition Y) = equiv-eq-Π-Decomposition Y
--   pr2 (extensionality-Π-Decomposition Y) = is-equiv-equiv-eq-Π-Decomposition Y

--   eq-equiv-Π-Decomposition :
--     (Y : Π-Decomposition l2 l3 A) → equiv-Π-Decomposition X Y → (X ＝ Y)
--   eq-equiv-Π-Decomposition Y =
--     map-inv-equiv (extensionality-Π-Decomposition Y)
-- ```

-- ### Invariance of Π-decompositions under equivalences

-- ```agda
-- module _
--   {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
--   where

--   equiv-tr-Π-Decomposition :
--     {l3 l4 : Level} → Π-Decomposition l3 l4 A ≃ Π-Decomposition l3 l4 B
--   equiv-tr-Π-Decomposition =
--     equiv-tot
--       ( λ X →
--         equiv-tot
--           ( λ Y →
--             equiv-precomp-equiv (inv-equiv e) (total-Fam-Inhabited-Types Y)))

--   map-equiv-tr-Π-Decomposition :
--     {l3 l4 : Level} → Π-Decomposition l3 l4 A → Π-Decomposition l3 l4 B
--   map-equiv-tr-Π-Decomposition = map-equiv equiv-tr-Π-Decomposition
-- ```

-- ### Characterization of equality of set-indexed Π-Decompositions

-- ```agda
-- equiv-Set-Indexed-Π-Decomposition :
--   {l1 l2 l3 l4 l5 : Level} {A : UU l1}
--   (X : Set-Indexed-Π-Decomposition l2 l3 A)
--   (Y : Set-Indexed-Π-Decomposition l4 l5 A) →
--   UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
-- equiv-Set-Indexed-Π-Decomposition X Y =
--   Σ ( indexing-type-Set-Indexed-Π-Decomposition X ≃
--       indexing-type-Set-Indexed-Π-Decomposition Y)
--     ( λ e →
--       Σ ( (x : indexing-type-Set-Indexed-Π-Decomposition X) →
--           cotype-Set-Indexed-Π-Decomposition X x ≃
--           cotype-Set-Indexed-Π-Decomposition Y (map-equiv e x))
--         ( λ f →
--           ( ( map-equiv (equiv-Σ (cotype-Set-Indexed-Π-Decomposition Y) e f)) ∘
--             ( map-matching-correspondence-Set-Indexed-Π-Decomposition X)) ~
--           ( map-matching-correspondence-Set-Indexed-Π-Decomposition Y)))

-- module _
--   {l1 l2 l3 : Level} {A : UU l1} (X : Set-Indexed-Π-Decomposition l2 l3 A)
--   where

--   id-equiv-Set-Indexed-Π-Decomposition : equiv-Set-Indexed-Π-Decomposition X X
--   pr1 id-equiv-Set-Indexed-Π-Decomposition = id-equiv
--   pr1 (pr2 id-equiv-Set-Indexed-Π-Decomposition) x = id-equiv
--   pr2 (pr2 id-equiv-Set-Indexed-Π-Decomposition) = refl-htpy

--   is-contr-total-equiv-Set-Indexed-Π-Decomposition :
--     is-contr
--       ( Σ ( Set-Indexed-Π-Decomposition l2 l3 A)
--           ( equiv-Set-Indexed-Π-Decomposition X))
--   is-contr-total-equiv-Set-Indexed-Π-Decomposition =
--     is-contr-total-Eq-structure
--       ( λ U Vf e →
--         Σ ( (x : indexing-type-Set-Indexed-Π-Decomposition X) →
--             cotype-Set-Indexed-Π-Decomposition X x ≃
--             type-Inhabited-Type (pr1 Vf (map-equiv e x)))
--           ( λ f →
--             ( ( map-equiv
--                 ( equiv-Σ (λ u → type-Inhabited-Type (pr1 Vf u)) e f)) ∘
--               ( map-matching-correspondence-Set-Indexed-Π-Decomposition X)) ~
--             ( map-equiv (pr2 Vf))))
--       ( is-contr-total-equiv-Set (indexing-set-Set-Indexed-Π-Decomposition X))
--       ( pair (indexing-set-Set-Indexed-Π-Decomposition X) id-equiv)
--       ( is-contr-total-Eq-structure
--         ( λ V g f →
--           ( ( map-equiv
--               ( equiv-Σ (λ y → type-Inhabited-Type (V y)) id-equiv f)) ∘
--             ( map-matching-correspondence-Set-Indexed-Π-Decomposition X)) ~
--           ( map-equiv g))
--         ( is-contr-total-equiv-Fam-Inhabited-Types
--           ( inhabited-cotype-Set-Indexed-Π-Decomposition X))
--         ( pair
--           ( inhabited-cotype-Set-Indexed-Π-Decomposition X)
--           ( id-equiv-Fam-Inhabited-Types
--             ( inhabited-cotype-Set-Indexed-Π-Decomposition X)))
--         ( is-contr-total-htpy-equiv
--           ( matching-correspondence-Set-Indexed-Π-Decomposition X)))

--   equiv-eq-Set-Indexed-Π-Decomposition :
--     (Y : Set-Indexed-Π-Decomposition l2 l3 A) →
--     (X ＝ Y) → equiv-Set-Indexed-Π-Decomposition X Y
--   equiv-eq-Set-Indexed-Π-Decomposition .X refl =
--     id-equiv-Set-Indexed-Π-Decomposition

--   is-equiv-equiv-eq-Set-Indexed-Π-Decomposition :
--     (Y : Set-Indexed-Π-Decomposition l2 l3 A) →
--     is-equiv (equiv-eq-Set-Indexed-Π-Decomposition Y)
--   is-equiv-equiv-eq-Set-Indexed-Π-Decomposition =
--     fundamental-theorem-id
--       is-contr-total-equiv-Set-Indexed-Π-Decomposition
--       equiv-eq-Set-Indexed-Π-Decomposition

--   extensionality-Set-Indexed-Π-Decomposition :
--     (Y : Set-Indexed-Π-Decomposition l2 l3 A) →
--     (X ＝ Y) ≃ equiv-Set-Indexed-Π-Decomposition X Y
--   pr1 (extensionality-Set-Indexed-Π-Decomposition Y) =
--     equiv-eq-Set-Indexed-Π-Decomposition Y
--   pr2 (extensionality-Set-Indexed-Π-Decomposition Y) =
--     is-equiv-equiv-eq-Set-Indexed-Π-Decomposition Y

--   eq-equiv-Set-Indexed-Π-Decomposition :
--     (Y : Set-Indexed-Π-Decomposition l2 l3 A) →
--     equiv-Set-Indexed-Π-Decomposition X Y → (X ＝ Y)
--   eq-equiv-Set-Indexed-Π-Decomposition Y =
--     map-inv-equiv (extensionality-Set-Indexed-Π-Decomposition Y)
-- ```

-- ### Iterated Π-decompositions

-- #### Characterization of identity type for fibered double Π-decompositions

-- ```agda
-- module _
--   {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
--   {A : UU l1} (X : fibered-Π-Decomposition l2 l3 l4 l5 A)
--   (Y : fibered-Π-Decomposition l6 l7 l8 l9 A)
--   where

--   equiv-fst-fibered-Π-Decomposition :
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
--   equiv-fst-fibered-Π-Decomposition =
--     equiv-Π-Decomposition
--     ( fst-fibered-Π-Decomposition X)
--     ( fst-fibered-Π-Decomposition Y)

--   equiv-snd-fibered-Π-Decomposition :
--     (e : equiv-fst-fibered-Π-Decomposition) →
--     UU (l4 ⊔ l5 ⊔ l6 ⊔ l8 ⊔ l9)
--   equiv-snd-fibered-Π-Decomposition e =
--     equiv-Π-Decomposition
--       ( map-equiv-tr-Π-Decomposition
--         ( equiv-indexing-type-equiv-Π-Decomposition
--           ( fst-fibered-Π-Decomposition X)
--           ( fst-fibered-Π-Decomposition Y)
--           ( e))
--         ( snd-fibered-Π-Decomposition X))
--       ( snd-fibered-Π-Decomposition Y)

--   equiv-fibered-Π-Decomposition :
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
--   equiv-fibered-Π-Decomposition =
--     Σ ( equiv-fst-fibered-Π-Decomposition)
--       ( equiv-snd-fibered-Π-Decomposition)

--   fst-equiv-fibered-Π-Decomposition :
--     (e : equiv-fibered-Π-Decomposition) →
--     equiv-fst-fibered-Π-Decomposition
--   fst-equiv-fibered-Π-Decomposition = pr1

--   snd-equiv-fibered-Π-Decomposition :
--     (e : equiv-fibered-Π-Decomposition) →
--     equiv-snd-fibered-Π-Decomposition
--       (fst-equiv-fibered-Π-Decomposition e)
--   snd-equiv-fibered-Π-Decomposition = pr2

-- module _
--   { l1 l2 l3 l4 l5 : Level} {A : UU l1}
--   ( D : fibered-Π-Decomposition l2 l3 l4 l5 A)
--   where

--   private
--     X = fst-fibered-Π-Decomposition D
--     Y = snd-fibered-Π-Decomposition D

--   is-contr-total-equiv-fibered-Π-Decomposition :
--     is-contr
--       ( Σ ( fibered-Π-Decomposition l2 l3 l4 l5 A)
--           ( equiv-fibered-Π-Decomposition D))
--   is-contr-total-equiv-fibered-Π-Decomposition =
--     is-contr-total-Eq-structure
--       ( λ X' Y' e →
--         equiv-snd-fibered-Π-Decomposition D (X' , Y') e)
--       ( is-contr-total-equiv-Π-Decomposition X)
--       ( X , id-equiv-Π-Decomposition X)
--       ( is-contr-total-Eq-structure
--         ( λ U Vs e →
--           ( Σ ( ( u : indexing-type-Π-Decomposition Y) →
--                 cotype-Π-Decomposition Y u ≃
--                 type-Inhabited-Type (pr1 Vs (map-equiv e u)))
--              ( λ f →
--                ( ( ( map-equiv-Σ (λ u → type-Inhabited-Type (pr1 Vs u)) e f) ∘
--                    ( map-matching-correspondence-Π-Decomposition Y)) ~
--                  ( map-equiv (pr2 Vs))))))
--         ( is-contr-total-equiv (indexing-type-Π-Decomposition Y))
--         ( pair (indexing-type-Π-Decomposition Y) id-equiv)
--         ( is-contr-total-Eq-structure
--           ( λ V f g →
--             ( ( map-equiv-Σ (λ u → type-Inhabited-Type (V u)) id-equiv g) ∘
--               ( map-matching-correspondence-Π-Decomposition Y)) ~
--               ( pr1 f))
--           ( is-contr-total-equiv-Fam-Inhabited-Types
--             ( inhabited-cotype-Π-Decomposition Y))
--           ( pair
--             ( inhabited-cotype-Π-Decomposition Y)
--             ( id-equiv-Fam-Inhabited-Types
--               ( inhabited-cotype-Π-Decomposition Y)))
--             ( is-contr-total-htpy-equiv
--               ( matching-correspondence-Π-Decomposition Y))))

--   id-equiv-fibered-Π-Decomposition :
--     equiv-fibered-Π-Decomposition D D
--   pr1 id-equiv-fibered-Π-Decomposition = id-equiv-Π-Decomposition X
--   pr1 (pr2 id-equiv-fibered-Π-Decomposition) = id-equiv
--   pr1 (pr2 (pr2 id-equiv-fibered-Π-Decomposition)) x = id-equiv
--   pr2 (pr2 (pr2 id-equiv-fibered-Π-Decomposition)) = refl-htpy

--   equiv-eq-fibered-Π-Decomposition :
--     (D' : fibered-Π-Decomposition l2 l3 l4 l5 A) →
--     (D ＝ D') → equiv-fibered-Π-Decomposition D D'
--   equiv-eq-fibered-Π-Decomposition .D refl =
--     id-equiv-fibered-Π-Decomposition

--   is-equiv-equiv-eq-fibered-Π-Decomposition :
--     (D' : fibered-Π-Decomposition l2 l3 l4 l5 A) →
--     is-equiv (equiv-eq-fibered-Π-Decomposition D')
--   is-equiv-equiv-eq-fibered-Π-Decomposition =
--     fundamental-theorem-id
--       is-contr-total-equiv-fibered-Π-Decomposition
--       equiv-eq-fibered-Π-Decomposition

--   extensionality-fibered-Π-Decomposition :
--     (D' : fibered-Π-Decomposition l2 l3 l4 l5 A) →
--     (D ＝ D') ≃ equiv-fibered-Π-Decomposition D D'
--   pr1 (extensionality-fibered-Π-Decomposition D') =
--     equiv-eq-fibered-Π-Decomposition D'
--   pr2 (extensionality-fibered-Π-Decomposition D') =
--     is-equiv-equiv-eq-fibered-Π-Decomposition D'

--   eq-equiv-fibered-Π-Decomposition :
--     (D' : fibered-Π-Decomposition l2 l3 l4 l5 A) →
--     (equiv-fibered-Π-Decomposition D D') → (D ＝ D')
--   eq-equiv-fibered-Π-Decomposition D' =
--     map-inv-equiv (extensionality-fibered-Π-Decomposition D')
-- ```

-- #### Characterization of identity type for displayed double Π-decompositions

-- ```agda
-- module _
--   {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
--   {A : UU l1} (X : displayed-Π-Decomposition l2 l3 l4 l5 A)
--   (Y : displayed-Π-Decomposition l6 l7 l8 l9 A)
--   where

--   equiv-fst-displayed-Π-Decomposition :
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l6 ⊔ l7)
--   equiv-fst-displayed-Π-Decomposition =
--     equiv-Π-Decomposition
--     ( fst-displayed-Π-Decomposition X)
--     ( fst-displayed-Π-Decomposition Y)

--   equiv-snd-displayed-Π-Decomposition :
--     (e : equiv-fst-displayed-Π-Decomposition) →
--     UU (l2 ⊔ l4 ⊔ l5 ⊔ l7 ⊔ l8 ⊔ l9)
--   equiv-snd-displayed-Π-Decomposition e =
--     ( x : indexing-type-fst-displayed-Π-Decomposition X) →
--     equiv-Π-Decomposition
--       ( map-equiv-tr-Π-Decomposition
--         ( equiv-cotype-equiv-Π-Decomposition
--           ( fst-displayed-Π-Decomposition X)
--           ( fst-displayed-Π-Decomposition Y)
--           ( e)
--           ( x))
--         ( snd-displayed-Π-Decomposition X x))
--       ( snd-displayed-Π-Decomposition Y
--         ( map-equiv-indexing-type-equiv-Π-Decomposition
--           ( fst-displayed-Π-Decomposition X)
--           ( fst-displayed-Π-Decomposition Y)
--           ( e)
--           ( x)))

--   equiv-displayed-Π-Decomposition :
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9)
--   equiv-displayed-Π-Decomposition =
--     Σ ( equiv-fst-displayed-Π-Decomposition)
--       ( equiv-snd-displayed-Π-Decomposition)

--   fst-equiv-displayed-Π-Decomposition :
--     (e : equiv-displayed-Π-Decomposition) →
--     equiv-fst-displayed-Π-Decomposition
--   fst-equiv-displayed-Π-Decomposition = pr1

--   snd-equiv-displayed-Π-Decomposition :
--     (e : equiv-displayed-Π-Decomposition) →
--     equiv-snd-displayed-Π-Decomposition
--       ( fst-equiv-displayed-Π-Decomposition e)
--   snd-equiv-displayed-Π-Decomposition = pr2

-- module _
--   { l1 l2 l3 l4 l5 : Level} {A : UU l1}
--   ( disp-D : displayed-Π-Decomposition l2 l3 l4 l5 A)
--   where

--   private
--     X = fst-displayed-Π-Decomposition disp-D
--     f-Y = snd-displayed-Π-Decomposition disp-D

--   is-contr-total-equiv-displayed-Π-Decomposition :
--     is-contr
--       ( Σ ( displayed-Π-Decomposition l2 l3 l4 l5 A)
--           ( equiv-displayed-Π-Decomposition disp-D))
--   is-contr-total-equiv-displayed-Π-Decomposition =
--     is-contr-total-Eq-structure
--       ( λ X' f-Y' e → equiv-snd-displayed-Π-Decomposition
--         ( disp-D)
--         ( pair X' f-Y')
--         ( e))
--       ( is-contr-total-equiv-Π-Decomposition X)
--       ( pair X (id-equiv-Π-Decomposition X))
--       ( is-contr-equiv
--         ( Π-total-fam (λ x → _))
--         ( inv-distributive-Π-Σ)
--         ( is-contr-Π (λ x → is-contr-total-equiv-Π-Decomposition (f-Y x))))

--   id-equiv-displayed-Π-Decomposition :
--     equiv-displayed-Π-Decomposition disp-D disp-D
--   pr1 id-equiv-displayed-Π-Decomposition = id-equiv-Π-Decomposition X
--   pr1 (pr2 id-equiv-displayed-Π-Decomposition x) = id-equiv
--   pr1 (pr2 (pr2 id-equiv-displayed-Π-Decomposition x)) y = id-equiv
--   pr2 (pr2 (pr2 id-equiv-displayed-Π-Decomposition x)) = refl-htpy

--   equiv-eq-displayed-Π-Decomposition :
--     (disp-D' : displayed-Π-Decomposition l2 l3 l4 l5 A) →
--     (disp-D ＝ disp-D') → equiv-displayed-Π-Decomposition disp-D disp-D'
--   equiv-eq-displayed-Π-Decomposition .disp-D refl =
--     id-equiv-displayed-Π-Decomposition

--   is-equiv-equiv-eq-displayed-Π-Decomposition :
--     (disp-D' : displayed-Π-Decomposition l2 l3 l4 l5 A) →
--     is-equiv (equiv-eq-displayed-Π-Decomposition disp-D')
--   is-equiv-equiv-eq-displayed-Π-Decomposition =
--     fundamental-theorem-id
--       is-contr-total-equiv-displayed-Π-Decomposition
--       equiv-eq-displayed-Π-Decomposition

--   extensionality-displayed-Π-Decomposition :
--     (disp-D' : displayed-Π-Decomposition l2 l3 l4 l5 A) →
--     (disp-D ＝ disp-D') ≃ equiv-displayed-Π-Decomposition disp-D disp-D'
--   pr1 (extensionality-displayed-Π-Decomposition D) =
--     equiv-eq-displayed-Π-Decomposition D
--   pr2 (extensionality-displayed-Π-Decomposition D) =
--     is-equiv-equiv-eq-displayed-Π-Decomposition D

--   eq-equiv-displayed-Π-Decomposition :
--     (disp-D' : displayed-Π-Decomposition l2 l3 l4 l5 A) →
--     (equiv-displayed-Π-Decomposition disp-D disp-D') → (disp-D ＝ disp-D')
--   eq-equiv-displayed-Π-Decomposition D =
--     map-inv-equiv
--       (extensionality-displayed-Π-Decomposition D)
-- ```

-- #### Equivalence between fibered double Π-Decompositions and displayed double Π-Decompositions

-- ```agda
-- module _
--   {l1 l2 l3 l4 l5 : Level} {A : UU l1}
--   (fib-D : fibered-Π-Decomposition l2 l3 l4 l5 A)
--   where

--   private
--     X = indexing-type-fst-fibered-Π-Decomposition fib-D
--     Y = cotype-fst-fibered-Π-Decomposition fib-D
--     Y-Inhabited-Type = inhabited-cotype-fst-fibered-Π-Decomposition fib-D
--     e = matching-correspondence-Π-Decomposition
--       ( fst-fibered-Π-Decomposition fib-D)
--     U = indexing-type-snd-fibered-Π-Decomposition fib-D
--     V = cotype-snd-fibered-Π-Decomposition fib-D
--     V-Inhabited-Type = inhabited-cotype-snd-fibered-Π-Decomposition fib-D
--     f = matching-correspondence-Π-Decomposition
--       ( snd-fibered-Π-Decomposition fib-D)

--   matching-correspondence-displayed-fibered-Π-Decomposition :
--      A ≃ Σ U (λ u → Σ (V u) (λ v → Y (map-inv-equiv f (u , v))))
--   matching-correspondence-displayed-fibered-Π-Decomposition =
--     equivalence-reasoning
--     A ≃ Σ X Y by e
--       ≃ Σ ( Σ U V) (λ uv → Y ((map-inv-equiv f) uv))
--         by inv-equiv ( equiv-Σ-equiv-base Y (inv-equiv f))
--       ≃ Σ U ( λ u → Σ (V u) (λ v → Y (map-inv-equiv f (u , v))))
--         by associative-Σ U V (λ uv → Y (map-inv-equiv f uv))

--   map-displayed-fibered-Π-Decomposition :
--     displayed-Π-Decomposition l4 (l3 ⊔ l5) l5 l3 A
--   pr1 (pr1 map-displayed-fibered-Π-Decomposition) = U
--   pr1 (pr2 (pr1 map-displayed-fibered-Π-Decomposition)) u =
--     Σ-Inhabited-Type
--       ( V-Inhabited-Type u)
--       ( λ v → Y-Inhabited-Type (map-inv-equiv f (u , v)))
--   pr2 (pr2 (pr1 map-displayed-fibered-Π-Decomposition)) =
--     matching-correspondence-displayed-fibered-Π-Decomposition
--   pr1 (pr2 map-displayed-fibered-Π-Decomposition u) = V u
--   pr1 (pr2 (pr2 map-displayed-fibered-Π-Decomposition u)) v =
--     Y-Inhabited-Type (map-inv-equiv f (u , v))
--   pr2 (pr2 (pr2 map-displayed-fibered-Π-Decomposition u)) = id-equiv

-- module _
--   {l1 l2 l3 l4 l5 : Level} {A : UU l1}
--   (disp-D : displayed-Π-Decomposition l2 l3 l4 l5 A)
--   where

--   private
--     M = indexing-type-fst-displayed-Π-Decomposition disp-D
--     N = cotype-fst-displayed-Π-Decomposition disp-D
--     s = matching-correspondence-Π-Decomposition
--       ( fst-displayed-Π-Decomposition disp-D)
--     P = indexing-type-snd-displayed-Π-Decomposition disp-D
--     Q-Inhabited-Type =
--       inhabited-cotype-snd-displayed-Π-Decomposition disp-D
--     Q = cotype-snd-displayed-Π-Decomposition disp-D
--     t = matching-correspondence-snd-displayed-Π-Decomposition disp-D

--   matching-correspondence-inv-displayed-fibered-Π-Decomposition :
--     A ≃ Σ (Σ M P) (λ (m , p) → Q m p)
--   matching-correspondence-inv-displayed-fibered-Π-Decomposition =
--     equivalence-reasoning
--     A ≃ Σ M N by s
--       ≃ Σ M (λ m → Σ (P m) (Q m))by equiv-Σ (λ m → Σ (P m) (Q m)) id-equiv t
--       ≃ Σ (Σ M P) (λ (m , p) → Q m p)
--       by inv-associative-Σ
--         ( M)
--         ( λ z → P z)
--         ( λ z → Q (pr1 z) (pr2 z))

--   map-inv-displayed-fibered-Π-Decomposition :
--     fibered-Π-Decomposition (l2 ⊔ l4) l5 l2 l4 A
--   pr1 (pr1 map-inv-displayed-fibered-Π-Decomposition) = Σ M P
--   pr1 (pr2 (pr1 map-inv-displayed-fibered-Π-Decomposition)) (m , p) =
--     Q-Inhabited-Type m p
--   pr2 (pr2 (pr1 map-inv-displayed-fibered-Π-Decomposition)) =
--     matching-correspondence-inv-displayed-fibered-Π-Decomposition
--   pr1 (pr2 map-inv-displayed-fibered-Π-Decomposition) = M
--   pr1 (pr1 (pr2 (pr2 map-inv-displayed-fibered-Π-Decomposition)) m) = P m
--   pr2 (pr1 (pr2 (pr2 map-inv-displayed-fibered-Π-Decomposition)) m) =
--     ind-trunc-Prop
--       ( λ n → trunc-Prop (P m))
--       ( λ n → unit-trunc-Prop (pr1 (map-equiv (t m) n)))
--       ( is-inhabited-cotype-Π-Decomposition
--         ( fst-displayed-Π-Decomposition disp-D)
--         ( m))
--   pr2 (pr2 (pr2 map-inv-displayed-fibered-Π-Decomposition)) = id-equiv

-- module _
--   {l1 l : Level} {A : UU l1}
--   (fib-D : fibered-Π-Decomposition l l l l A)
--   where

--   private
--     X = indexing-type-fst-fibered-Π-Decomposition fib-D
--     Y = cotype-fst-fibered-Π-Decomposition fib-D
--     e = matching-correspondence-Π-Decomposition
--       ( fst-fibered-Π-Decomposition fib-D)
--     U = indexing-type-snd-fibered-Π-Decomposition fib-D
--     V = cotype-snd-fibered-Π-Decomposition fib-D
--     f = matching-correspondence-Π-Decomposition
--       ( snd-fibered-Π-Decomposition fib-D)
--     disp-D = map-displayed-fibered-Π-Decomposition fib-D
--     M = indexing-type-fst-displayed-Π-Decomposition disp-D
--     N = cotype-fst-displayed-Π-Decomposition disp-D
--     s = matching-correspondence-Π-Decomposition
--       ( fst-displayed-Π-Decomposition disp-D)
--     P = indexing-type-snd-displayed-Π-Decomposition disp-D
--     Q = cotype-snd-displayed-Π-Decomposition disp-D
--     t = matching-correspondence-snd-displayed-Π-Decomposition disp-D

--     htpy-matching-correspondence :
--       ( map-equiv
--         ( ( equiv-Σ Y (inv-equiv f) (λ (m , p) → id-equiv)) ∘e
--           ( matching-correspondence-inv-displayed-fibered-Π-Decomposition
--             ( disp-D)))) ~
--       ( map-equiv e)
--     htpy-matching-correspondence a =
--       htpy-eq-equiv
--         ( right-inverse-law-equiv (equiv-Σ-equiv-base Y (inv-equiv f)))
--         ( map-equiv e a)

--   isretr-map-inv-displayed-fibered-Π-Decomposition :
--      map-inv-displayed-fibered-Π-Decomposition
--       ( map-displayed-fibered-Π-Decomposition fib-D) ＝ fib-D
--   isretr-map-inv-displayed-fibered-Π-Decomposition =
--     eq-equiv-fibered-Π-Decomposition
--       ( map-inv-displayed-fibered-Π-Decomposition
--         ( map-displayed-fibered-Π-Decomposition fib-D))
--       ( fib-D)
--       ( ( ( inv-equiv f) ,
--           ( ( λ x → id-equiv) ,
--             ( htpy-matching-correspondence))) ,
--         ( ( id-equiv) ,
--           ( ( λ u → id-equiv) ,
--             ( λ a → refl))))

-- module _
--   {l1 l : Level} {A : UU l1}
--   (disp-D : displayed-Π-Decomposition l l l l A)
--   where

--   private
--     M = indexing-type-fst-displayed-Π-Decomposition disp-D
--     N = cotype-fst-displayed-Π-Decomposition disp-D
--     s = matching-correspondence-Π-Decomposition
--       ( fst-displayed-Π-Decomposition disp-D)
--     P = indexing-type-snd-displayed-Π-Decomposition disp-D
--     Q = cotype-snd-displayed-Π-Decomposition disp-D
--     t = matching-correspondence-snd-displayed-Π-Decomposition disp-D
--     fib-D = map-inv-displayed-fibered-Π-Decomposition disp-D
--     X = indexing-type-fst-fibered-Π-Decomposition fib-D
--     Y = cotype-fst-fibered-Π-Decomposition fib-D
--     e = matching-correspondence-Π-Decomposition
--       ( fst-fibered-Π-Decomposition fib-D)
--     U = indexing-type-snd-fibered-Π-Decomposition fib-D
--     V = cotype-snd-fibered-Π-Decomposition fib-D
--     f = matching-correspondence-Π-Decomposition
--       ( snd-fibered-Π-Decomposition fib-D)

--     htpy-matching-correspondence :
--       map-equiv
--         ( equiv-Σ N id-equiv (inv-equiv ∘ t) ∘e
--           matching-correspondence-displayed-fibered-Π-Decomposition
--             (fib-D)) ~
--       map-equiv s
--     htpy-matching-correspondence x =
--       ( ap
--         ( λ f → map-equiv (equiv-tot (inv-equiv ∘ t)) f)
--         ( inv-map-eq-transpose-equiv
--           ( associative-Σ M P Y)
--           ( inv
--             ( map-eq-transpose-equiv
--               ( equiv-Σ-equiv-base Y (inv-equiv id-equiv))
--               ( inv
--                 ( map-eq-transpose-equiv
--                   ( associative-Σ M P Y)
--                   ( issec-map-inv-associative-Σ M P Y
--                     ( map-equiv (equiv-tot t ∘e s) x)))))))) ∙
--       ( inv
--         ( preserves-comp-tot
--           ( map-equiv ∘ t)
--           ( map-inv-equiv ∘ t)
--           ( map-equiv s x)) ∙
--       ( tot-htpy (λ z → isretr-map-inv-equiv (t z)) (map-equiv s x) ∙
--       ( tot-id
--         ( λ z → cotype-fst-displayed-Π-Decomposition disp-D z)
--         ( map-equiv s x))))

--   issec-map-inv-displayed-fibered-Π-Decomposition :
--     ( map-displayed-fibered-Π-Decomposition
--       {l1} {l} {l} {l} {l} {A} fib-D) ＝
--     disp-D
--   issec-map-inv-displayed-fibered-Π-Decomposition =
--      eq-equiv-displayed-Π-Decomposition
--       ( map-displayed-fibered-Π-Decomposition fib-D)
--       ( disp-D)
--       ( ( ( id-equiv) ,
--           ( ( inv-equiv ∘ t) ,
--             ( htpy-matching-correspondence))) ,
--         ( λ (m : M) →
--           ( ( id-equiv) ,
--             ( ( λ (p : P m) → id-equiv) ,
--               ( refl-htpy)))))

-- is-equiv-map-displayed-fibered-Π-Decomposition :
--   {l1 l : Level} → {A : UU l1} →
--   is-equiv
--     ( map-displayed-fibered-Π-Decomposition {l1} {l} {l} {l} {l} {A})
-- is-equiv-map-displayed-fibered-Π-Decomposition =
--   is-equiv-has-inverse
--     ( map-inv-displayed-fibered-Π-Decomposition)
--     ( issec-map-inv-displayed-fibered-Π-Decomposition)
--     ( isretr-map-inv-displayed-fibered-Π-Decomposition)

-- equiv-displayed-fibered-Π-Decomposition :
--   {l1 l : Level} → {A : UU l1} →
--   fibered-Π-Decomposition l l l l A ≃
--   displayed-Π-Decomposition l l l l A
-- pr1 equiv-displayed-fibered-Π-Decomposition =
--   map-displayed-fibered-Π-Decomposition
-- pr2 equiv-displayed-fibered-Π-Decomposition =
--   is-equiv-map-displayed-fibered-Π-Decomposition
-- ```
