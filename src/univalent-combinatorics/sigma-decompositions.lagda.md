# Finite Σ-decompositions of finite types

```agda
module univalent-combinatorics.sigma-decompositions where

open import foundation.sigma-decompositions public
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-universal-property-equivalences
open import foundation.embeddings
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.relaxed-sigma-decompositions
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import univalent-combinatorics.decidable-equivalence-relations
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
open import univalent-combinatorics.type-duality
```

</details>

## Definition

```agda
Σ-Decomposition-Finite-Type :
  {l : Level} → (l1 l2 : Level) → Finite-Type l → UU (l ⊔ lsuc l1 ⊔ lsuc l2)
Σ-Decomposition-Finite-Type l1 l2 A =
  Σ ( Finite-Type l1)
    ( λ X →
      Σ ( type-Finite-Type X → Inhabited-Finite-Type l2)
        ( λ Y → type-Finite-Type A ≃ (Σ (type-Finite-Type X) (λ x → type-Inhabited-Finite-Type (Y x)))))

module _
  {l l1 l2 : Level} (A : Finite-Type l) (D : Σ-Decomposition-Finite-Type l1 l2 A)
  where

  finite-indexing-type-Σ-Decomposition-Finite-Type : Finite-Type l1
  finite-indexing-type-Σ-Decomposition-Finite-Type = pr1 D

  indexing-type-Σ-Decomposition-Finite-Type : UU l1
  indexing-type-Σ-Decomposition-Finite-Type =
    type-Finite-Type finite-indexing-type-Σ-Decomposition-Finite-Type

  is-finite-indexing-type-Σ-Decomposition-Finite-Type :
    is-finite (indexing-type-Σ-Decomposition-Finite-Type)
  is-finite-indexing-type-Σ-Decomposition-Finite-Type =
    is-finite-type-Finite-Type finite-indexing-type-Σ-Decomposition-Finite-Type

  finite-inhabited-cotype-Σ-Decomposition-Finite-Type :
    Family-Of-Inhabited-Finite-Types l2 finite-indexing-type-Σ-Decomposition-Finite-Type
  finite-inhabited-cotype-Σ-Decomposition-Finite-Type = pr1 (pr2 D)

  finite-cotype-Σ-Decomposition-Finite-Type :
    type-Finite-Type finite-indexing-type-Σ-Decomposition-Finite-Type → Finite-Type l2
  finite-cotype-Σ-Decomposition-Finite-Type =
    finite-type-Family-Of-Inhabited-Finite-Types
      finite-indexing-type-Σ-Decomposition-Finite-Type
      finite-inhabited-cotype-Σ-Decomposition-Finite-Type

  cotype-Σ-Decomposition-Finite-Type :
    type-Finite-Type finite-indexing-type-Σ-Decomposition-Finite-Type → UU l2
  cotype-Σ-Decomposition-Finite-Type x = type-Finite-Type (finite-cotype-Σ-Decomposition-Finite-Type x)

  is-finite-cotype-Σ-Decomposition-Finite-Type :
    (x : type-Finite-Type finite-indexing-type-Σ-Decomposition-Finite-Type) →
    is-finite (cotype-Σ-Decomposition-Finite-Type x)
  is-finite-cotype-Σ-Decomposition-Finite-Type x =
    is-finite-type-Finite-Type (finite-cotype-Σ-Decomposition-Finite-Type x)

  is-inhabited-cotype-Σ-Decomposition-Finite-Type :
    (x : type-Finite-Type finite-indexing-type-Σ-Decomposition-Finite-Type) →
    is-inhabited (cotype-Σ-Decomposition-Finite-Type x)
  is-inhabited-cotype-Σ-Decomposition-Finite-Type x =
    is-inhabited-type-Inhabited-Finite-Type
      ( finite-inhabited-cotype-Σ-Decomposition-Finite-Type x)

  inhabited-cotype-Σ-Decomposition-Finite-Type :
    Fam-Inhabited-Types l2 indexing-type-Σ-Decomposition-Finite-Type
  pr1 (inhabited-cotype-Σ-Decomposition-Finite-Type x) =
    cotype-Σ-Decomposition-Finite-Type x
  pr2 (inhabited-cotype-Σ-Decomposition-Finite-Type x) =
    is-inhabited-cotype-Σ-Decomposition-Finite-Type x

  matching-correspondence-Σ-Decomposition-Finite-Type :
    type-Finite-Type A ≃ Σ indexing-type-Σ-Decomposition-Finite-Type cotype-Σ-Decomposition-Finite-Type
  matching-correspondence-Σ-Decomposition-Finite-Type = pr2 (pr2 D)

  map-matching-correspondence-Σ-Decomposition-Finite-Type :
    type-Finite-Type A → Σ indexing-type-Σ-Decomposition-Finite-Type cotype-Σ-Decomposition-Finite-Type
  map-matching-correspondence-Σ-Decomposition-Finite-Type =
    map-equiv matching-correspondence-Σ-Decomposition-Finite-Type

  Σ-Decomposition-Σ-Decomposition-Finite-Type :
    Σ-Decomposition l1 l2 (type-Finite-Type A)
  pr1 Σ-Decomposition-Σ-Decomposition-Finite-Type =
    indexing-type-Σ-Decomposition-Finite-Type
  pr1 (pr2 Σ-Decomposition-Σ-Decomposition-Finite-Type) =
    inhabited-cotype-Σ-Decomposition-Finite-Type
  pr2 (pr2 Σ-Decomposition-Σ-Decomposition-Finite-Type) =
    matching-correspondence-Σ-Decomposition-Finite-Type
```

### Fibered double finite Σ-decompositions

```agda
fibered-Σ-Decomposition-Finite-Type :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : Finite-Type l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
fibered-Σ-Decomposition-Finite-Type l2 l3 l4 l5 A =
  Σ ( Σ-Decomposition-Finite-Type l2 l3 A)
    ( λ D →
      Σ-Decomposition-Finite-Type l4 l5 (finite-indexing-type-Σ-Decomposition-Finite-Type A D))
```

### Displayed double Σ-decompositions

```agda
displayed-Σ-Decomposition-Finite-Type :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : Finite-Type l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
displayed-Σ-Decomposition-Finite-Type l2 l3 l4 l5 A =
  ( Σ ( Σ-Decomposition-Finite-Type l2 l3 A)
      ( λ D → (u : indexing-type-Σ-Decomposition-Finite-Type A D) →
        Σ-Decomposition-Finite-Type l4 l5 (finite-cotype-Σ-Decomposition-Finite-Type A D u)))
```

## Properties

### Finite Σ-Decomposition as a relaxed Σ-Decomposition with conditions

```agda
equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-Finite-Type :
  {l1 l2 l3 : Level} (A : Finite-Type l1) →
  Σ-Decomposition-Finite-Type l2 l3 A ≃
  Σ ( Relaxed-Σ-Decomposition l2 l3 (type-Finite-Type A))
    ( λ D →
      is-finite (indexing-type-Relaxed-Σ-Decomposition D) ×
      ((x : indexing-type-Relaxed-Σ-Decomposition D) →
        is-finite (cotype-Relaxed-Σ-Decomposition D x) ×
        is-inhabited (cotype-Relaxed-Σ-Decomposition D x)))
pr1 ( equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-Finite-Type A) D =
  ( indexing-type-Σ-Decomposition-Finite-Type A D ,
    ( cotype-Σ-Decomposition-Finite-Type A D) ,
    ( matching-correspondence-Σ-Decomposition-Finite-Type A D)) ,
    ( is-finite-indexing-type-Σ-Decomposition-Finite-Type A D) ,
    ( λ x → is-finite-cotype-Σ-Decomposition-Finite-Type A D x ,
            is-inhabited-cotype-Σ-Decomposition-Finite-Type A D x)
pr2 ( equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-Finite-Type A) =
  is-equiv-is-invertible
    ( λ X →
      ( pr1 (pr1 X) , pr1 (pr2 X)) ,
      ( ( λ x →
          ( pr1 (pr2 (pr1 X)) x , pr1 (pr2 (pr2 X) x)) ,
          ( pr2 (pr2 (pr2 X) x))) ,
        ( pr2 (pr2 (pr1 X)))))
    ( refl-htpy)
    ( refl-htpy)
```

### Equivalence between finite surjection and finite Σ-decomposition

```agda
module _
  {l : Level} (A : Finite-Type l)
  where

  equiv-finite-surjection-Σ-Decomposition-Finite-Type :
    Σ-Decomposition-Finite-Type l l A ≃ Σ (Finite-Type l) (λ B → (type-Finite-Type A) ↠ (type-Finite-Type B))
  equiv-finite-surjection-Σ-Decomposition-Finite-Type =
    equiv-Σ
      ( λ B → type-Finite-Type A ↠ type-Finite-Type B)
      ( id-equiv)
      ( λ X → inv-equiv (equiv-surjection-𝔽-family-finite-inhabited-type A X))
```

### Equivalence between finite decidable equivalence relations and finite Σ-decompositions

```agda
  equiv-Decidable-Equivalence-Relation-Finite-Type-Σ-Decomposition-Finite-Type :
    Σ-Decomposition-Finite-Type l l A ≃
    Decidable-Equivalence-Relation-Finite-Type l A
  equiv-Decidable-Equivalence-Relation-Finite-Type-Σ-Decomposition-Finite-Type =
    inv-equiv (equiv-Surjection-Finite-Type-Decidable-Equivalence-Relation-Finite-Type A) ∘e
    equiv-finite-surjection-Σ-Decomposition-Finite-Type
```

### The type of all finite Σ-Decomposition is finite

```agda
  is-finite-Σ-Decomposition-Finite-Type :
    is-finite (Σ-Decomposition-Finite-Type l l A)
  is-finite-Σ-Decomposition-Finite-Type =
    is-finite-equiv
      ( inv-equiv equiv-Decidable-Equivalence-Relation-Finite-Type-Σ-Decomposition-Finite-Type)
      ( is-finite-Decidable-Equivalence-Relation-Finite-Type A)
```

### Characterization of the equality of finite Σ-decompositions

```agda
module _
  {l1 l2 l3 : Level} (A : Finite-Type l1)
  where

  is-finite-Σ-Decomposition :
    subtype (l2 ⊔ l3) (Σ-Decomposition l2 l3 (type-Finite-Type A))
  is-finite-Σ-Decomposition D =
    Σ-Prop
      ( is-finite-Prop (indexing-type-Σ-Decomposition D))
      ( λ _ →
        Π-Prop
          ( indexing-type-Σ-Decomposition D)
          ( λ x → is-finite-Prop (cotype-Σ-Decomposition D x)))

  map-Σ-Decomposition-Finite-Type-subtype-is-finite :
    type-subtype is-finite-Σ-Decomposition → Σ-Decomposition-Finite-Type l2 l3 A
  map-Σ-Decomposition-Finite-Type-subtype-is-finite ((X , (Y , e)) , (fin-X , fin-Y)) =
    ( ( X , fin-X) ,
        ( ( λ x →
            ( (type-Inhabited-Type (Y x)) , (fin-Y x)) ,
              (is-inhabited-type-Inhabited-Type (Y x))) ,
        e))

  map-inv-Σ-Decomposition-Finite-Type-subtype-is-finite :
    Σ-Decomposition-Finite-Type l2 l3 A → type-subtype is-finite-Σ-Decomposition
  map-inv-Σ-Decomposition-Finite-Type-subtype-is-finite ((X , fin-X) , (Y , e)) =
    ( ( X ,
        ( ( λ x → inhabited-type-Inhabited-Finite-Type (Y x)) ,
          ( e))) ,
      (fin-X , (λ x → is-finite-Inhabited-Finite-Type (Y x))))

  equiv-Σ-Decomposition-Finite-Type-is-finite-subtype :
    type-subtype is-finite-Σ-Decomposition ≃ Σ-Decomposition-Finite-Type l2 l3 A
  pr1 (equiv-Σ-Decomposition-Finite-Type-is-finite-subtype) =
    map-Σ-Decomposition-Finite-Type-subtype-is-finite
  pr2 (equiv-Σ-Decomposition-Finite-Type-is-finite-subtype) =
    is-equiv-is-invertible
      map-inv-Σ-Decomposition-Finite-Type-subtype-is-finite
      refl-htpy
      refl-htpy

  is-emb-Σ-Decomposition-Σ-Decomposition-Finite-Type :
    is-emb (Σ-Decomposition-Σ-Decomposition-Finite-Type {l1} {l2} {l3} A)
  is-emb-Σ-Decomposition-Σ-Decomposition-Finite-Type =
    is-emb-triangle-is-equiv
      ( Σ-Decomposition-Σ-Decomposition-Finite-Type A)
      ( pr1)
      ( map-inv-equiv ( equiv-Σ-Decomposition-Finite-Type-is-finite-subtype))
      ( refl-htpy)
      ( is-equiv-map-inv-equiv
        ( equiv-Σ-Decomposition-Finite-Type-is-finite-subtype))
      ( is-emb-inclusion-subtype (is-finite-Σ-Decomposition))

  emb-Σ-Decomposition-Σ-Decomposition-Finite-Type :
    Σ-Decomposition-Finite-Type l2 l3 A ↪ Σ-Decomposition l2 l3 (type-Finite-Type A)
  pr1 (emb-Σ-Decomposition-Σ-Decomposition-Finite-Type) =
    Σ-Decomposition-Σ-Decomposition-Finite-Type A
  pr2 (emb-Σ-Decomposition-Σ-Decomposition-Finite-Type) =
    is-emb-Σ-Decomposition-Σ-Decomposition-Finite-Type

equiv-Σ-Decomposition-Finite-Type :
  {l1 l2 l3 l4 l5 : Level} (A : Finite-Type l1)
  (X : Σ-Decomposition-Finite-Type l2 l3 A) (Y : Σ-Decomposition-Finite-Type l4 l5 A) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
equiv-Σ-Decomposition-Finite-Type A X Y =
  equiv-Σ-Decomposition
    ( Σ-Decomposition-Σ-Decomposition-Finite-Type A X)
    ( Σ-Decomposition-Σ-Decomposition-Finite-Type A Y)

module _
  {l1 l2 l3 : Level} (A : Finite-Type l1)
  (X : Σ-Decomposition-Finite-Type l2 l3 A) (Y : Σ-Decomposition-Finite-Type l2 l3 A)
  where

  extensionality-Σ-Decomposition-Finite-Type :
    (X ＝ Y) ≃ equiv-Σ-Decomposition-Finite-Type A X Y
  extensionality-Σ-Decomposition-Finite-Type =
    extensionality-Σ-Decomposition
      ( Σ-Decomposition-Σ-Decomposition-Finite-Type A X)
      ( Σ-Decomposition-Σ-Decomposition-Finite-Type A Y) ∘e
    equiv-ap-emb (emb-Σ-Decomposition-Σ-Decomposition-Finite-Type A)

  eq-equiv-Σ-Decomposition-Finite-Type :
    equiv-Σ-Decomposition-Finite-Type A X Y → (X ＝ Y)
  eq-equiv-Σ-Decomposition-Finite-Type =
    map-inv-equiv (extensionality-Σ-Decomposition-Finite-Type)
```

### Iterated finite Σ-Decomposition

#### Fibered finite Σ-Decomposition as a subtype

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (A : Finite-Type l1)
  where

  is-finite-fibered-Σ-Decomposition :
    subtype (l2 ⊔ l3 ⊔ l4 ⊔ l5)
      ( fibered-Σ-Decomposition l2 l3 l4 l5 (type-Finite-Type A))
  is-finite-fibered-Σ-Decomposition D =
    Σ-Prop
      ( is-finite-Σ-Decomposition A ( fst-fibered-Σ-Decomposition D))
      ( λ p →
        is-finite-Σ-Decomposition
          ( indexing-type-fst-fibered-Σ-Decomposition D ,
            (pr1 p))
          ( snd-fibered-Σ-Decomposition D))

  equiv-fibered-Σ-Decomposition-Finite-Type-is-finite-subtype :
    type-subtype is-finite-fibered-Σ-Decomposition ≃
    fibered-Σ-Decomposition-Finite-Type l2 l3 l4 l5 A
  equiv-fibered-Σ-Decomposition-Finite-Type-is-finite-subtype =
    equiv-Σ
      ( λ D →
        Σ-Decomposition-Finite-Type l4 l5 ( finite-indexing-type-Σ-Decomposition-Finite-Type A D))
      ( equiv-Σ-Decomposition-Finite-Type-is-finite-subtype A)
      ( λ x →
        equiv-Σ-Decomposition-Finite-Type-is-finite-subtype
        ( indexing-type-Σ-Decomposition
          ( inclusion-subtype (is-finite-Σ-Decomposition A) x) ,
            pr1
              ( is-in-subtype-inclusion-subtype
                ( is-finite-Σ-Decomposition A)
                (x)))) ∘e
      interchange-Σ-Σ
        ( λ D D' p →
          type-Prop
            ( is-finite-Σ-Decomposition
              ( indexing-type-Σ-Decomposition D ,
                pr1 p)
              ( D')))
```

#### Displayed finite Σ-Decomposition as a subtype

```agda
  is-finite-displayed-Σ-Decomposition :
    subtype (l2 ⊔ l3 ⊔ l4 ⊔ l5)
      ( displayed-Σ-Decomposition l2 l3 l4 l5 (type-Finite-Type A))
  is-finite-displayed-Σ-Decomposition D =
    Σ-Prop
      ( is-finite-Σ-Decomposition A (fst-displayed-Σ-Decomposition D))
      ( λ p →
        Π-Prop
          ( indexing-type-fst-displayed-Σ-Decomposition D)
          ( λ x →
            is-finite-Σ-Decomposition
              ( cotype-fst-displayed-Σ-Decomposition D x ,
                pr2 p x)
              ( snd-displayed-Σ-Decomposition D x)))

  equiv-displayed-Σ-Decomposition-Finite-Type-is-finite-subtype :
    type-subtype is-finite-displayed-Σ-Decomposition ≃
    displayed-Σ-Decomposition-Finite-Type l2 l3 l4 l5 A
  equiv-displayed-Σ-Decomposition-Finite-Type-is-finite-subtype =
    equiv-Σ
      ( λ D →
        ( x : indexing-type-Σ-Decomposition-Finite-Type A D) →
        ( Σ-Decomposition-Finite-Type l4 l5 ( finite-cotype-Σ-Decomposition-Finite-Type A D x)))
      ( equiv-Σ-Decomposition-Finite-Type-is-finite-subtype A)
      ( λ D1 →
        equiv-Π
          ( _)
          ( id-equiv)
          ( λ x →
            equiv-Σ-Decomposition-Finite-Type-is-finite-subtype
            ( ( cotype-Σ-Decomposition
                ( inclusion-subtype (is-finite-Σ-Decomposition A) D1)
                ( x)) ,
              pr2
                ( is-in-subtype-inclusion-subtype
                  ( is-finite-Σ-Decomposition A) D1) x)) ∘e
          inv-distributive-Π-Σ) ∘e
      interchange-Σ-Σ _
```

#### Fibered finite Σ-decompositions and displayed finite Σ-Decomposition are equivalent

```agda
module _
  {l1 l : Level} (A : Finite-Type l1)
  (D : fibered-Σ-Decomposition l l l l (type-Finite-Type A))
  where

  map-is-finite-displayed-fibered-Σ-Decomposition :
    type-Prop (is-finite-fibered-Σ-Decomposition A D) →
    type-Prop (is-finite-displayed-Σ-Decomposition A
      (map-equiv equiv-displayed-fibered-Σ-Decomposition D))
  pr1 (pr1 (map-is-finite-displayed-fibered-Σ-Decomposition p)) =
    pr1 (pr2 p)
  pr2 (pr1 (map-is-finite-displayed-fibered-Σ-Decomposition p)) =
    λ u → is-finite-Σ (pr2 (pr2 p) u) (λ v → (pr2 (pr1 p)) _)
  pr1 (pr2 (map-is-finite-displayed-fibered-Σ-Decomposition p) u) =
    pr2 (pr2 p) u
  pr2 (pr2 (map-is-finite-displayed-fibered-Σ-Decomposition p) u) =
    λ v → (pr2 (pr1 p)) _

  map-inv-is-finite-displayed-fibered-Σ-Decomposition :
    type-Prop (is-finite-displayed-Σ-Decomposition A
      (map-equiv equiv-displayed-fibered-Σ-Decomposition D)) →
    type-Prop (is-finite-fibered-Σ-Decomposition A D)
  pr1 (pr1 (map-inv-is-finite-displayed-fibered-Σ-Decomposition p)) =
    is-finite-equiv
      ( inv-equiv (matching-correspondence-snd-fibered-Σ-Decomposition D))
      ( is-finite-Σ (pr1 (pr1 p)) λ u → (pr1 (pr2 p u)))
  pr2 (pr1 (map-inv-is-finite-displayed-fibered-Σ-Decomposition p)) =
    map-inv-equiv
      ( equiv-precomp-Π
        ( inv-equiv ( matching-correspondence-snd-fibered-Σ-Decomposition D))
        ( λ z → is-finite (cotype-fst-fibered-Σ-Decomposition D z)))
      λ uv → pr2 (pr2 p (pr1 uv)) (pr2 uv)
  pr1 (pr2 (map-inv-is-finite-displayed-fibered-Σ-Decomposition p)) =
    pr1 (pr1 p)
  pr2 (pr2 (map-inv-is-finite-displayed-fibered-Σ-Decomposition p)) =
    λ u → pr1 (pr2 p u)

  equiv-is-finite-displayed-fibered-Σ-Decomposition :
    type-Prop (is-finite-fibered-Σ-Decomposition A D) ≃
    type-Prop (is-finite-displayed-Σ-Decomposition A
      (map-equiv equiv-displayed-fibered-Σ-Decomposition D))
  equiv-is-finite-displayed-fibered-Σ-Decomposition =
    equiv-iff-is-prop
      ( is-prop-type-Prop (is-finite-fibered-Σ-Decomposition A D))
      ( is-prop-type-Prop
        ( is-finite-displayed-Σ-Decomposition A
          ( map-equiv equiv-displayed-fibered-Σ-Decomposition D)))
      ( map-is-finite-displayed-fibered-Σ-Decomposition)
      ( map-inv-is-finite-displayed-fibered-Σ-Decomposition)

equiv-displayed-fibered-Σ-Decomposition-Finite-Type :
  {l1 l : Level} (A : Finite-Type l1) →
  fibered-Σ-Decomposition-Finite-Type l l l l A ≃ displayed-Σ-Decomposition-Finite-Type l l l l A
equiv-displayed-fibered-Σ-Decomposition-Finite-Type A =
  equiv-displayed-Σ-Decomposition-Finite-Type-is-finite-subtype A ∘e
    ( equiv-Σ
        ( λ x → type-Prop (is-finite-displayed-Σ-Decomposition A x))
        ( equiv-displayed-fibered-Σ-Decomposition)
        ( equiv-is-finite-displayed-fibered-Σ-Decomposition A) ∘e
      inv-equiv ( equiv-fibered-Σ-Decomposition-Finite-Type-is-finite-subtype A))
```
