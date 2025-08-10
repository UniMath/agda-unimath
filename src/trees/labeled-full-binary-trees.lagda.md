# Labeled full binary trees

```agda
module trees.labeled-full-binary-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections

open import trees.full-binary-trees
```

</details>

## Idea

For a type `X`, an
{{#concept "`X`-labeling" Disambiguation="of full binary trees" Agda=labeling-full-binary-tree}}
of a [full binary tree](trees.full-binary-trees.md) `T` is a map from the nodes
of `T` to `X`. A
{{#concept "labeled full binary tree" Agda=labeled-full-binary-tree}} is a pair
of a full binary tree and a labeling.

## Definition

```agda
module _
  {l : Level} (X : UU l)
  where

  labeling-full-binary-tree : (T : full-binary-tree) → UU l
  labeling-full-binary-tree T = node-full-binary-tree T → X

  labeled-full-binary-tree : UU l
  labeled-full-binary-tree =
    Σ full-binary-tree (λ T → labeling-full-binary-tree T)
```

### The weight of a labeled full binary tree

This is simply the weight of its underlying full binary tree.

```agda
  weight-labeled-full-binary-tree : labeled-full-binary-tree → ℕ
  weight-labeled-full-binary-tree (T , _) = weight-full-binary-tree T
```

### Computing transport of labelings along identifications of full binary trees

```agda
module _
  {l : Level} (X : UU l)
  where

  compute-tr-Eq-labeling-full-binary-tree :
    (U : labeled-full-binary-tree X) →
    (V : full-binary-tree) →
    Eq-full-binary-tree (pr1 U) V →
    labeling-full-binary-tree X V
  compute-tr-Eq-labeling-full-binary-tree
    (leaf-full-binary-tree , lab-U) leaf-full-binary-tree star star = lab-U star
  compute-tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree U U₁ , lab-U)
    (join-full-binary-tree V V₁) (p , q) (inl x) =
      compute-tr-Eq-labeling-full-binary-tree (U , λ y → lab-U (inl y)) V p x
  compute-tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree U U₁ , lab-U)
    (join-full-binary-tree V V₁) (p , q) (inr x) =
      compute-tr-Eq-labeling-full-binary-tree (U₁ , λ y → lab-U (inr y)) V₁ q x
```

### Characterizing the identity type of labeled full binary trees

```agda
module _
  {l : Level} (X : UU l)
  where

  Eq-htpy-labeled-full-binary-tree :
    (U V : labeled-full-binary-tree X) →
    Eq-full-binary-tree (pr1 U) (pr1 V) →
    UU l
  Eq-htpy-labeled-full-binary-tree U V p =
    compute-tr-Eq-labeling-full-binary-tree X U (pr1 V) p ~ pr2 V

  refl-compute-tr-Eq-labeling-full-binary-tree :
    (T : full-binary-tree) (f g : labeling-full-binary-tree X T) → f ＝ g →
    Eq-htpy-labeled-full-binary-tree (T , f) (T , g)
      (refl-Eq-full-binary-tree T)
  refl-compute-tr-Eq-labeling-full-binary-tree
    leaf-full-binary-tree f f refl star =
      refl
  refl-compute-tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree T T₁) f f refl (inl x) =
      refl-compute-tr-Eq-labeling-full-binary-tree T
      ( λ y → f (inl y)) (λ y → f (inl y)) refl x
  refl-compute-tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree T T₁) f f refl (inr x) =
      refl-compute-tr-Eq-labeling-full-binary-tree T₁
      ( λ y → f (inr y)) (λ y → f (inr y)) refl x

  eq-inl-compute-tr-Eq-labeling-full-binary-tree :
    (U V : full-binary-tree)
    (f : labeling-full-binary-tree X (join-full-binary-tree U V))
    (x : node-full-binary-tree U) →
    f (inl x) ＝ compute-tr-Eq-labeling-full-binary-tree X
      (U , λ y → f (inl y)) U
      (refl-Eq-full-binary-tree U) x
  eq-inl-compute-tr-Eq-labeling-full-binary-tree
    leaf-full-binary-tree _ f star = refl
  eq-inl-compute-tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree U U₁) _ f (inl x) =
      eq-inl-compute-tr-Eq-labeling-full-binary-tree U U₁ (λ z → f (inl z)) x
  eq-inl-compute-tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree U U₁) _ f (inr x) =
      eq-inl-compute-tr-Eq-labeling-full-binary-tree U₁ U lab x
        where
        lab : labeling-full-binary-tree X (join-full-binary-tree U₁ U)
        lab (inl y) = f (inl (inr y))
        lab (inr y) = f (inl (inl y))

  eq-inr-compute-tr-Eq-labeling-full-binary-tree : (U V : full-binary-tree)
    (f : labeling-full-binary-tree X (join-full-binary-tree U V))
    (x : node-full-binary-tree V) →
    f (inr x) ＝ compute-tr-Eq-labeling-full-binary-tree X
      (V , λ y → f (inr y)) V
      (refl-Eq-full-binary-tree V) x
  eq-inr-compute-tr-Eq-labeling-full-binary-tree
    _ leaf-full-binary-tree f star = refl
  eq-inr-compute-tr-Eq-labeling-full-binary-tree
    _ (join-full-binary-tree V V₁) f (inl x) =
      eq-inr-compute-tr-Eq-labeling-full-binary-tree V₁ V lab x
        where
        lab : labeling-full-binary-tree X (join-full-binary-tree V₁ V)
        lab (inl y) = f (inr (inl x))
        lab (inr y) = f (inr (inl y))
  eq-inr-compute-tr-Eq-labeling-full-binary-tree
    _ (join-full-binary-tree V V₁) f (inr x) =
      eq-inr-compute-tr-Eq-labeling-full-binary-tree V V₁ (λ z → f (inr z)) x

  inv-refl-compute-tr-Eq-labeling-full-binary-tree :
    (T : full-binary-tree) (f g : labeling-full-binary-tree X T) →
    Eq-htpy-labeled-full-binary-tree (T , f) (T , g)
      (refl-Eq-full-binary-tree T) →
    f ＝ g
  inv-refl-compute-tr-Eq-labeling-full-binary-tree leaf-full-binary-tree f g p =
    eq-htpy (λ x → p star)
  inv-refl-compute-tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree T T₁) f g p =
      eq-htpy htpy
        where
        htpy : f ~ g
        htpy (inl x) =
          eq-inl-compute-tr-Eq-labeling-full-binary-tree T T₁ f x ∙ p (inl x)
        htpy (inr x) =
          eq-inr-compute-tr-Eq-labeling-full-binary-tree T T₁ f x ∙ p (inr x)

  is-equiv-refl-compute-tr-Eq-labeling-full-binary-tree :
    (T : full-binary-tree) (f g : labeling-full-binary-tree X T) →
    is-equiv (refl-compute-tr-Eq-labeling-full-binary-tree T f g)
  pr1 (pr1 (is-equiv-refl-compute-tr-Eq-labeling-full-binary-tree T f g)) =
    inv-refl-compute-tr-Eq-labeling-full-binary-tree T f g
  pr2 (pr1 (is-equiv-refl-compute-tr-Eq-labeling-full-binary-tree
    leaf-full-binary-tree f g)) p = eq-htpy htpy
      where
      htpy :
        (refl-compute-tr-Eq-labeling-full-binary-tree
          leaf-full-binary-tree f g ∘
          pr1 (pr1 (is-equiv-refl-compute-tr-Eq-labeling-full-binary-tree
            leaf-full-binary-tree f g))) p ~
        p
      htpy star = ap {!   !} {!   !} ∙ {!   !}
  pr2 (pr1 (is-equiv-refl-compute-tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree T T₁) f g)) p = eq-htpy htpy
      where
      htpy :
        (refl-compute-tr-Eq-labeling-full-binary-tree
          (join-full-binary-tree T T₁) f g ∘
          pr1 (pr1 (is-equiv-refl-compute-tr-Eq-labeling-full-binary-tree
            (join-full-binary-tree T T₁) f g))) p ~
        p
      htpy (inl x) = {!   !}
      htpy (inr x) = {!   !}
  pr1 (pr2 (is-equiv-refl-compute-tr-Eq-labeling-full-binary-tree T f g)) =
    inv-refl-compute-tr-Eq-labeling-full-binary-tree T f g
  pr2 (pr2 (is-equiv-refl-compute-tr-Eq-labeling-full-binary-tree
    leaf-full-binary-tree f f)) refl = {!   !}
  pr2 (pr2 (is-equiv-refl-compute-tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree T T₁) f f)) refl = {!   !}

  Eq-labeled-full-binary-tree :
    labeled-full-binary-tree X → labeled-full-binary-tree X → UU l
  Eq-labeled-full-binary-tree (U , lab-U) (V , lab-V) =
    Σ
      ( Eq-full-binary-tree U V)
      ( Eq-htpy-labeled-full-binary-tree (U , lab-U) (V , lab-V))

  {-# TERMINATING #-}
  refl-Eq-htpy-labeled-full-binary-tree :
    (U : labeled-full-binary-tree X) →
    Eq-htpy-labeled-full-binary-tree U U (refl-Eq-full-binary-tree (pr1 U))
  refl-Eq-htpy-labeled-full-binary-tree (leaf-full-binary-tree , lab-U) star =
    refl
  refl-Eq-htpy-labeled-full-binary-tree
    (join-full-binary-tree U V , lab) (inl x) =
      refl-Eq-htpy-labeled-full-binary-tree (U , (λ y → lab (inl y))) x
  refl-Eq-htpy-labeled-full-binary-tree
    (join-full-binary-tree U V , lab) (inr x) =
      refl-Eq-htpy-labeled-full-binary-tree (V , (λ y → lab (inr y))) x

  Eq-eq-labeled-full-binary-tree :
    (U V : labeled-full-binary-tree X) →
    U ＝ V →
    Eq-labeled-full-binary-tree U V
  pr1 (Eq-eq-labeled-full-binary-tree U U refl) =
    refl-Eq-full-binary-tree (pr1 U)
  pr2 (Eq-eq-labeled-full-binary-tree U U refl) =
    refl-Eq-htpy-labeled-full-binary-tree U

  is-equiv-Eq-eq-labeled-full-binary-tree :
    (U V : labeled-full-binary-tree X) →
    is-equiv (Eq-eq-labeled-full-binary-tree U V)
  is-equiv-Eq-eq-labeled-full-binary-tree U =
    structure-identity-principle
    ( λ {x} f p → Eq-htpy-labeled-full-binary-tree U (x , f) p)
    ( refl-Eq-full-binary-tree (pr1 U))
    ( refl-Eq-htpy-labeled-full-binary-tree U)
    ( Eq-eq-labeled-full-binary-tree U)
    ( λ _ → is-equiv-Eq-eq-full-binary-tree)
    ( λ y → is-equiv-refl-compute-tr-Eq-labeling-full-binary-tree
      ( pr1 U) (pr2 U) y)

  equiv-Eq-eq-labeled-full-binary-tree :
    (U V : labeled-full-binary-tree X) →
    (U ＝ V) ≃
    Eq-labeled-full-binary-tree U V
  pr1 (equiv-Eq-eq-labeled-full-binary-tree U V) =
    Eq-eq-labeled-full-binary-tree U V
  pr2 (equiv-Eq-eq-labeled-full-binary-tree U V) =
    is-equiv-Eq-eq-labeled-full-binary-tree U V

  eq-Eq-labeled-full-binary-tree :
    (U V : labeled-full-binary-tree X) →
    Eq-labeled-full-binary-tree U V →
    U ＝ V
  eq-Eq-labeled-full-binary-tree U V =
    map-inv-equiv (equiv-Eq-eq-labeled-full-binary-tree U V)
```
