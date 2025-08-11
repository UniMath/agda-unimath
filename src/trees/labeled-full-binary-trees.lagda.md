# Labeled full binary trees

```agda
{-# OPTIONS --lossy-unification #-}

module trees.labeled-full-binary-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-higher-identifications
open import foundation.transport-along-identifications-dependent-functions
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.transport-along-identifications

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

  tr-Eq-labeling-full-binary-tree :
    (U : labeled-full-binary-tree X)
    (V : full-binary-tree) →
    Eq-full-binary-tree (pr1 U) V →
    labeling-full-binary-tree X V
  tr-Eq-labeling-full-binary-tree
    (leaf-full-binary-tree , lab-U) leaf-full-binary-tree star star = lab-U star
  tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree U U₁ , lab-U)
    (join-full-binary-tree V V₁) (p , q) (inl x) =
      tr-Eq-labeling-full-binary-tree (U , λ y → lab-U (inl y)) V p x
  tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree U U₁ , lab-U)
    (join-full-binary-tree V V₁) (p , q) (inr x) =
      tr-Eq-labeling-full-binary-tree (U₁ , λ y → lab-U (inr y)) V₁ q x
```

### Characterizing identifications of labeled full binary trees

```agda
module _
  {l : Level} (X : UU l)
  where

  Eq-htpy-labeled-full-binary-tree :
    (U V : labeled-full-binary-tree X) →
    Eq-full-binary-tree (pr1 U) (pr1 V) →
    UU l
  Eq-htpy-labeled-full-binary-tree U V p =
    tr-Eq-labeling-full-binary-tree X U (pr1 V) p ~ pr2 V

  Eq-labeled-full-binary-tree :
    labeled-full-binary-tree X → labeled-full-binary-tree X → UU l
  Eq-labeled-full-binary-tree U V =
    Σ ( Eq-full-binary-tree (pr1 U) (pr1 V))
      ( Eq-htpy-labeled-full-binary-tree U V)

  refl-tr-Eq-labeling-full-binary-tree :
    (T : full-binary-tree) (f g : labeling-full-binary-tree X T) →
    f ＝ g →
    Eq-htpy-labeled-full-binary-tree (T , f) (T , g)
      (refl-Eq-full-binary-tree T)
  refl-tr-Eq-labeling-full-binary-tree
    leaf-full-binary-tree f f refl star =
      refl
  refl-tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree T T₁) f f refl (inl x) =
      refl-tr-Eq-labeling-full-binary-tree T
      ( λ y → f (inl y)) (λ y → f (inl y)) refl x
  refl-tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree T T₁) f f refl (inr x) =
      refl-tr-Eq-labeling-full-binary-tree T₁
      ( λ y → f (inr y)) (λ y → f (inr y)) refl x

  {-# TERMINATING #-}
  compute-tr-refl-Eq-labeling-full-binary-tree :
    (U : labeled-full-binary-tree X) →
    pr2 U ~
    tr-Eq-labeling-full-binary-tree X U (pr1 U)
      (refl-Eq-full-binary-tree (pr1 U))
  compute-tr-refl-Eq-labeling-full-binary-tree
    (leaf-full-binary-tree , _) star = refl
  compute-tr-refl-Eq-labeling-full-binary-tree
    (join-full-binary-tree L R , lab) (inl x) =
    compute-tr-refl-Eq-labeling-full-binary-tree (L , (λ y → lab (inl y))) x
  compute-tr-refl-Eq-labeling-full-binary-tree
    (join-full-binary-tree L R , lab) (inr x) =
    compute-tr-refl-Eq-labeling-full-binary-tree (R , (λ y → lab (inr y))) x

  refl-Eq-htpy-labeled-full-binary-tree :
    (T : full-binary-tree) (f : labeling-full-binary-tree X T) →
    Eq-htpy-labeled-full-binary-tree (T , f) (T , f) (refl-Eq-full-binary-tree T)
  refl-Eq-htpy-labeled-full-binary-tree T f =
    inv-htpy (compute-tr-refl-Eq-labeling-full-binary-tree (T , f))

  compute-refl-Eq-refl-tr-Eq-labeled-full-binary-tree :
    (T : full-binary-tree) (f : labeling-full-binary-tree X T) →
    refl-tr-Eq-labeling-full-binary-tree T f f refl ＝
    refl-Eq-htpy-labeled-full-binary-tree T f
  compute-refl-Eq-refl-tr-Eq-labeled-full-binary-tree leaf-full-binary-tree f =
    refl
  compute-refl-Eq-refl-tr-Eq-labeled-full-binary-tree
    (join-full-binary-tree L R) f =
    eq-htpy htpy
      where
      htpy :
        refl-tr-Eq-labeling-full-binary-tree (join-full-binary-tree L R)
          f f refl ~
        refl-Eq-htpy-labeled-full-binary-tree (join-full-binary-tree L R) f
      htpy (inl x) = htpy-eq (compute-refl-Eq-refl-tr-Eq-labeled-full-binary-tree L (λ y → f (inl y))) x
      htpy (inr x) = htpy-eq (compute-refl-Eq-refl-tr-Eq-labeled-full-binary-tree R (λ y → f (inr y))) x

  compute-tr-Eq-labeling-full-binary-tree' :
    (U : labeled-full-binary-tree X)
    (V : full-binary-tree)
    (p : pr1 U ＝ V) →
    tr (labeling-full-binary-tree X) p (pr2 U) ~
    tr-Eq-labeling-full-binary-tree X U V (Eq-eq-full-binary-tree p)
  compute-tr-Eq-labeling-full-binary-tree'
    (leaf-full-binary-tree , lab) leaf-full-binary-tree refl star = refl
  compute-tr-Eq-labeling-full-binary-tree'
    (join-full-binary-tree V W , lab)
    (join-full-binary-tree V W) refl =
      compute-tr-refl-Eq-labeling-full-binary-tree
      ( join-full-binary-tree V W , lab)

  refl-Eq-labeled-full-binary-tree :
    (T : labeled-full-binary-tree X) → Eq-labeled-full-binary-tree T T
  pr1 (refl-Eq-labeled-full-binary-tree (T , _)) = refl-Eq-full-binary-tree T
  pr2 (refl-Eq-labeled-full-binary-tree (T , lab)) =
    refl-tr-Eq-labeling-full-binary-tree T lab lab refl

  compute-tr-Eq-labeling-full-binary-tree :
    (U V : labeled-full-binary-tree X) (p : Eq-labeled-full-binary-tree U V) →
    dependent-identification
      (labeling-full-binary-tree X)
      (eq-Eq-full-binary-tree (pr1 U) (pr1 V) (pr1 p))
      (pr2 U) (pr2 V)
  compute-tr-Eq-labeling-full-binary-tree
    (leaf-full-binary-tree , lab-U) (leaf-full-binary-tree , lab-V) (star , p) =
      eq-htpy (λ x → p star)
  compute-tr-Eq-labeling-full-binary-tree
    (join-full-binary-tree U U₁ , lab-U) (join-full-binary-tree V V₁ , lab-V)
    (p , q) =
      eq-htpy htpy
        where
        htpy :
          tr (labeling-full-binary-tree X)
            (eq-Eq-full-binary-tree
              (join-full-binary-tree U U₁)
              (join-full-binary-tree V V₁) p)
            lab-U ~
          lab-V
        htpy =
          compute-tr-Eq-labeling-full-binary-tree'
          ( join-full-binary-tree U U₁ , lab-U)
          ( join-full-binary-tree V V₁)
          ( eq-Eq-full-binary-tree
            ( join-full-binary-tree U U₁)
            ( join-full-binary-tree V V₁)
            p) ∙h
          ( λ x → ap (λ r → tr-Eq-labeling-full-binary-tree X
            ( join-full-binary-tree U U₁ , lab-U)
            ( join-full-binary-tree V V₁) r x)
              ( eq-is-prop (is-prop-Eq-full-binary-tree
                ( join-full-binary-tree U U₁)
                ( join-full-binary-tree V V₁)))) ∙h
          q

  Eq-eq-labeled-full-binary-tree :
    (U V : labeled-full-binary-tree X) →
    U ＝ V →
    Eq-labeled-full-binary-tree U V
  Eq-eq-labeled-full-binary-tree U U refl = refl-Eq-labeled-full-binary-tree U

  inv-refl-tr-Eq-labeling-full-binary-tree :
    (T : full-binary-tree) (f g : labeling-full-binary-tree X T) →
    Eq-htpy-labeled-full-binary-tree (T , f) (T , g)
      (refl-Eq-full-binary-tree T) →
    f ＝ g
  inv-refl-tr-Eq-labeling-full-binary-tree T f g p =
    eq-htpy (compute-tr-refl-Eq-labeling-full-binary-tree (T , f) ∙h p)

  is-section-inv-refl-tr-Eq-labeling-full-binary-tree :
    (T : full-binary-tree) (f g : labeling-full-binary-tree X T) →
    is-section
      (refl-tr-Eq-labeling-full-binary-tree T f g)
      (inv-refl-tr-Eq-labeling-full-binary-tree T f g)
  is-section-inv-refl-tr-Eq-labeling-full-binary-tree T f g p =
    eq-htpy {!   !}

  is-retraction-inv-refl-tr-Eq-labeling-full-binary-tree :
    (T : full-binary-tree) (f : labeling-full-binary-tree X T) →
      (inv-refl-tr-Eq-labeling-full-binary-tree T f f ∘
        refl-tr-Eq-labeling-full-binary-tree T f f)
        refl ＝
      refl
  is-retraction-inv-refl-tr-Eq-labeling-full-binary-tree T f =
    equational-reasoning
    ( inv-refl-tr-Eq-labeling-full-binary-tree T f f ∘
      refl-tr-Eq-labeling-full-binary-tree T f f)
      refl
    ＝ inv-refl-tr-Eq-labeling-full-binary-tree T f f
      ( refl-Eq-htpy-labeled-full-binary-tree T f)
      by ap (inv-refl-tr-Eq-labeling-full-binary-tree T f f)
        ( compute-refl-Eq-refl-tr-Eq-labeled-full-binary-tree T f)
    ＝ refl
      by {!   !}

  is-equiv-refl-tr-Eq-labeling-full-binary-tree :
    (T : full-binary-tree) (f g : labeling-full-binary-tree X T) →
    is-equiv (refl-tr-Eq-labeling-full-binary-tree T f g)
  pr1 (pr1 (is-equiv-refl-tr-Eq-labeling-full-binary-tree T f g)) =
    inv-refl-tr-Eq-labeling-full-binary-tree T f g
  pr2 (pr1 (is-equiv-refl-tr-Eq-labeling-full-binary-tree T f g)) =
    is-section-inv-refl-tr-Eq-labeling-full-binary-tree T f g
  pr1 (pr2 (is-equiv-refl-tr-Eq-labeling-full-binary-tree T f g)) =
    inv-refl-tr-Eq-labeling-full-binary-tree T f g
  pr2 (pr2 (is-equiv-refl-tr-Eq-labeling-full-binary-tree T f f)) refl =
    is-retraction-inv-refl-tr-Eq-labeling-full-binary-tree T f

  is-equiv-Eq-eq-labeled-full-binary-tree :
    (U V : labeled-full-binary-tree X) →
    is-equiv (Eq-eq-labeled-full-binary-tree U V)
  is-equiv-Eq-eq-labeled-full-binary-tree U =
    structure-identity-principle
    ( λ {T} lab p → Eq-htpy-labeled-full-binary-tree U (T , lab) p)
    ( refl-Eq-full-binary-tree (pr1 U))
    ( refl-tr-Eq-labeling-full-binary-tree (pr1 U) (pr2 U) (pr2 U) refl)
    ( Eq-eq-labeled-full-binary-tree U)
    ( λ T → is-equiv-Eq-eq-full-binary-tree)
    ( λ lab → is-equiv-refl-tr-Eq-labeling-full-binary-tree (pr1 U) (pr2 U) lab)
```
