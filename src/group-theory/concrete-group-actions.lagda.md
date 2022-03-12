# Concrete group actions

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.concrete-group-actions where

open import group-theory.concrete-groups public
open import synthetic-homotopy-theory.circle public
```

## Idea

Given a concrete group `G`, a concrete action of `G` on a type is defined to be a type family over `BG`. Given a type family `X` over `BG`, the type being acted on is the type `X *`, and the action of `G` on `X *` is given by transport.

More generally, a concrete action of `G` on objects of shape `a : A` is a pointed map `BG -> A`

## Definition

```agda
module _
  {ℓ' ℓ : Level} (G : Concrete-Group ℓ') (A : UU ℓ)
  where
  
  action-Concrete-Group : UU (ℓ' ⊔ ℓ)
  action-Concrete-Group = classifying-type-Concrete-Group G → A

  object-action-Concrete-Group : action-Concrete-Group → A
  object-action-Concrete-Group X = X (shape-Concrete-Group G)

_-Set_ : {ℓ' : Level} (G : Concrete-Group ℓ') (ℓ : Level) → UU (ℓ' ⊔ lsuc ℓ)
G -Set ℓ = action-Concrete-Group G (UU-Set ℓ)

module _
  {ℓ' ℓ : Level} (G : Concrete-Group ℓ') (X : G -Set ℓ)
  where

  set-action-Concrete-Group : UU-Set ℓ
  set-action-Concrete-Group = X (shape-Concrete-Group G)

  type-action-Concrete-Group : UU ℓ
  type-action-Concrete-Group = type-Set set-action-Concrete-Group

  _·G_ :
    (g : type-Concrete-Group G) →
    type-action-Concrete-Group → type-action-Concrete-Group
  g ·G x = tr (λ y → type-Set (X y)) g x

module _
  {ℓ : Level} (G : Concrete-Group ℓ) 
  where 

  private shG = shape-Concrete-Group G
  private BG = classifying-type-Concrete-Group G

  generalized-principal-torsor-action-Concrete-Group : BG → G -Set ℓ
  generalized-principal-torsor-action-Concrete-Group = Id-BG-Set G

  -- ref def:principaltorsor
  principal-torsor-action-Concrete-Group : G -Set ℓ
  principal-torsor-action-Concrete-Group =
    generalized-principal-torsor-action-Concrete-Group shG

  private P = principal-torsor-action-Concrete-Group

  -- ref def:adjointrep
  adjoint-rep-action-Concrete-Group : G -Set ℓ
  adjoint-rep-action-Concrete-Group X = Id-BG-Set G X X
  
  Ad = adjoint-rep-action-Concrete-Group

  k = pr1 (ind-𝕊¹ (λ _ → BG))

  free-loop-from-adjoint-rep : Σ (BG) (λ z → type-Set (Ad z)) → (𝕊¹ → BG)
  free-loop-from-adjoint-rep (pair z l) =
    map-apply-universal-property-𝕊¹ z l

  -- is-transitive-group-action : UU-Prop ℓ 
  -- is-transitive-group-action = 
```

### Substitution of concrete group actions

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  (f : hom-Concrete-Group G H)
  where

  subst-action-Concrete-Group :
    {l : Level} →
    action-Concrete-Group H (UU l) → action-Concrete-Group G (UU l)
  subst-action-Concrete-Group Y x =
    Y (classifying-map-hom-Concrete-Group G H f x)
```

### Morphisms of concrete group actions

```agda
module _
  {l : Level} (G : Concrete-Group l)
  where

  hom-action-Concrete-Group :
    {l1 l2 : Level} (X : action-Concrete-Group G (UU l1))
    (Y : action-Concrete-Group G (UU l2)) → UU (l ⊔ l1 ⊔ l2)
  hom-action-Concrete-Group X Y =
    (x : classifying-type-Concrete-Group G) → X x → Y x
```

### Operations on group actions

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  (f : hom-Concrete-Group G H)
  where

  left-adjoint-subst-action-Concrete-Group :
    {l : Level} → (classifying-type-Concrete-Group G → UU l) →
    (classifying-type-Concrete-Group H → UU (l1 ⊔ l2 ⊔ l))
  left-adjoint-subst-action-Concrete-Group X y =
    Σ ( classifying-type-Concrete-Group G)
      ( λ x → X x × Id (classifying-map-hom-Concrete-Group G H f x) y)

  contravariant-pushforward-action-Concrete-Group :
    {l : Level} → (classifying-type-Concrete-Group G → UU l) →
    (classifying-type-Concrete-Group H → UU (l1 ⊔ l2 ⊔ l))
  contravariant-pushforward-action-Concrete-Group X y =
    hom-action-Concrete-Group G X
      ( subst-action-Concrete-Group G H f (λ y → Id (shape-Concrete-Group H) y))
```

