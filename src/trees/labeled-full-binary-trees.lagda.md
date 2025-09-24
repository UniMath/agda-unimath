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
open import foundation.functoriality-dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.function-extensionality
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-higher-identifications
open import foundation.transport-along-identifications-dependent-functions
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.contractible-types
open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.subtypes
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

  tree-labeled-full-binary-tree : labeled-full-binary-tree → full-binary-tree
  tree-labeled-full-binary-tree = pr1

  labeling-labeled-full-binary-tree :
    (T : labeled-full-binary-tree) →
    labeling-full-binary-tree (tree-labeled-full-binary-tree T)
  labeling-labeled-full-binary-tree T = pr2 T
```

### The weight of a labeled full binary tree

This is simply the weight of its underlying full binary tree.

```agda
  weight-labeled-full-binary-tree : labeled-full-binary-tree → ℕ
  weight-labeled-full-binary-tree (T , _) = weight-full-binary-tree T
```

### Characterizing identifications of labeled full binary trees

```agda
module _
  {l : Level} (X : UU l)
  where

  {-# TERMINATING #-}
  htpy-labeled-full-binary-tree :
    (U V : labeled-full-binary-tree X) →
    Eq-full-binary-tree
      (tree-labeled-full-binary-tree X U)
      (tree-labeled-full-binary-tree X V) →
    UU l
  htpy-labeled-full-binary-tree
    (leaf-full-binary-tree , f) (leaf-full-binary-tree , g) star =
      f star ＝ g star
  htpy-labeled-full-binary-tree
    (join-full-binary-tree U U₁ , f) (join-full-binary-tree V V₁ , g) (p , q) =
      ( htpy-labeled-full-binary-tree
        ( U , (λ z → f (inl z))) (V , (λ z → g (inl z))) p) ×
      ( htpy-labeled-full-binary-tree
        ( U₁ , (λ z → f (inr z))) (V₁ , (λ z → g (inr z))) q)

  {-# TERMINATING #-}
  refl-htpy-labeled-full-binary-tree :
    (T : labeled-full-binary-tree X) →
    htpy-labeled-full-binary-tree T T
      (refl-Eq-full-binary-tree (tree-labeled-full-binary-tree X T))
  refl-htpy-labeled-full-binary-tree (leaf-full-binary-tree , f) = refl
  pr1 (refl-htpy-labeled-full-binary-tree (join-full-binary-tree T T₁ , f)) =
    refl-htpy-labeled-full-binary-tree (T , λ z → f (inl z))
  pr2 (refl-htpy-labeled-full-binary-tree (join-full-binary-tree T T₁ , f)) =
    refl-htpy-labeled-full-binary-tree (T₁ , λ z → f (inr z))

  Eq-labeled-full-binary-tree :
    labeled-full-binary-tree X → labeled-full-binary-tree X → UU l
  Eq-labeled-full-binary-tree U V =
    Σ ( Eq-full-binary-tree
        ( tree-labeled-full-binary-tree X U)
        ( tree-labeled-full-binary-tree X V))
      ( htpy-labeled-full-binary-tree U V)

  refl-Eq-labeled-full-binary-tree :
    (T : labeled-full-binary-tree X) → Eq-labeled-full-binary-tree T T
  refl-Eq-labeled-full-binary-tree (leaf-full-binary-tree , f) = (star , refl)
  pr1 (refl-Eq-labeled-full-binary-tree (join-full-binary-tree T T₁ , f)) =
    ( refl-Eq-full-binary-tree T , refl-Eq-full-binary-tree T₁)
  pr2 (refl-Eq-labeled-full-binary-tree (join-full-binary-tree T T₁ , f)) =
    refl-htpy-labeled-full-binary-tree ((join-full-binary-tree T T₁) , f)

  Eq-eq-labeled-full-binary-tree :
    (U V : labeled-full-binary-tree X) → U ＝ V →
    Eq-labeled-full-binary-tree U V
  Eq-eq-labeled-full-binary-tree U .U refl = refl-Eq-labeled-full-binary-tree U

  htpy-eq-labeled-full-binary-tree :
    (T : full-binary-tree) (f g : labeling-full-binary-tree X T) → f ＝ g →
    htpy-labeled-full-binary-tree (T , f) (T , g) (refl-Eq-full-binary-tree T)
  htpy-eq-labeled-full-binary-tree T f .f refl =
    refl-htpy-labeled-full-binary-tree (T , f)

  htpy-refl-labeled-full-binary-tree :
    (T : full-binary-tree) (f g : labeling-full-binary-tree X T) →
    htpy-labeled-full-binary-tree (T , f) (T , g) (refl-Eq-full-binary-tree T) →
    f ~ g
  htpy-refl-labeled-full-binary-tree leaf-full-binary-tree f g p star = p
  htpy-refl-labeled-full-binary-tree (join-full-binary-tree T T₁) f g (p , q) (inl x) =
    htpy-refl-labeled-full-binary-tree
      ( T)
      ( λ z → f (inl z))
      ( λ z → g (inl z))
      ( p)
      ( x)
  htpy-refl-labeled-full-binary-tree (join-full-binary-tree T T₁) f g (p , q) (inr x) =
    htpy-refl-labeled-full-binary-tree
      ( T₁)
      ( λ z → f (inr z))
      ( λ z → g (inr z))
      ( q)
      ( x)

  htpy'-refl-labeled-full-binary-tree :
    (T : full-binary-tree) (f g : labeling-full-binary-tree X T) →
    f ~ g →
    htpy-labeled-full-binary-tree (T , f) (T , g) (refl-Eq-full-binary-tree T)
  htpy'-refl-labeled-full-binary-tree leaf-full-binary-tree f g p = p star
  pr1 (htpy'-refl-labeled-full-binary-tree (join-full-binary-tree T T₁) f g p) =
    htpy'-refl-labeled-full-binary-tree
      ( T)
      ( λ z → f (inl z))
      ( λ z → g (inl z))
      ( λ x → p (inl x))
  pr2 (htpy'-refl-labeled-full-binary-tree (join-full-binary-tree T T₁) f g p) =
    htpy'-refl-labeled-full-binary-tree
      ( T₁)
      ( λ z → f (inr z))
      ( λ z → g (inr z))
      ( λ x → p (inr x))

  lemma-refl-htpy-labeled-full-binary-tree :
    (T : full-binary-tree) (f : labeling-full-binary-tree X T) →
    htpy-refl-labeled-full-binary-tree T f f
      (htpy'-refl-labeled-full-binary-tree T f f refl-htpy) ~
    refl-htpy
  lemma-refl-htpy-labeled-full-binary-tree leaf-full-binary-tree f star = refl
  lemma-refl-htpy-labeled-full-binary-tree (join-full-binary-tree T T₁) f (inl x) =
    lemma-refl-htpy-labeled-full-binary-tree T (λ z → f (inl z)) x
  lemma-refl-htpy-labeled-full-binary-tree (join-full-binary-tree T T₁) f (inr x) =
    lemma-refl-htpy-labeled-full-binary-tree T₁ (λ z → f (inr z)) x

  equiv-htpy'-refl-labeled-full-binary-tree :
    (T : full-binary-tree) (f g : labeling-full-binary-tree X T) →
    (f ~ g) ≃
    htpy-labeled-full-binary-tree (T , f) (T , g) (refl-Eq-full-binary-tree T)
  pr1 (equiv-htpy'-refl-labeled-full-binary-tree T f g) =
    htpy'-refl-labeled-full-binary-tree T f g
  pr1 (pr1 (pr2 (equiv-htpy'-refl-labeled-full-binary-tree T f g))) =
    htpy-refl-labeled-full-binary-tree T f g
  pr2 (pr1 (pr2 (equiv-htpy'-refl-labeled-full-binary-tree
    leaf-full-binary-tree f g))) p = refl
  pr2 (pr1 (pr2 (equiv-htpy'-refl-labeled-full-binary-tree
    (join-full-binary-tree T T₁) f g))) (p , q) =
    eq-pair
    ( pr2
      ( pr1
        ( pr2
          ( equiv-htpy'-refl-labeled-full-binary-tree T (λ z → f (inl z))
            ( λ z → g (inl z)))))
      ( p))
    ( pr2
      ( pr1
        ( pr2
          ( equiv-htpy'-refl-labeled-full-binary-tree T₁ (λ z → f (inr z))
            ( λ z → g (inr z)))))
      ( q))
  pr1 (pr2 (pr2 (equiv-htpy'-refl-labeled-full-binary-tree T f g))) =
    htpy-refl-labeled-full-binary-tree T f g
  pr2 (pr2 (pr2 (equiv-htpy'-refl-labeled-full-binary-tree
    leaf-full-binary-tree f g))) p =
    eq-htpy (λ x → refl)
  pr2 (pr2 (pr2 (equiv-htpy'-refl-labeled-full-binary-tree
    (join-full-binary-tree T T₁) f g))) =
    ind-htpy
      ( f)
      ( λ h q →
        htpy-refl-labeled-full-binary-tree
          ( join-full-binary-tree T T₁)
          ( f)
          ( h)
          ( htpy'-refl-labeled-full-binary-tree
            ( join-full-binary-tree T T₁)
            ( f)
            ( h)
            ( q)) ＝
        q)
      ( eq-htpy
        ( lemma-refl-htpy-labeled-full-binary-tree
          ( join-full-binary-tree T T₁)
          ( f)))

  abstract
    is-torsorial-htpy-labeled-full-binary-tree :
      (T : full-binary-tree) (f : labeling-full-binary-tree X T) →
      is-torsorial (λ g → htpy-labeled-full-binary-tree (T , f) (T , g)
        (refl-Eq-full-binary-tree T))
    is-torsorial-htpy-labeled-full-binary-tree T f =
      is-contr-equiv'
        ( Σ (labeling-full-binary-tree X T) (_~_ f))
        ( equiv-tot (equiv-htpy'-refl-labeled-full-binary-tree T f))
        ( is-torsorial-htpy f)

  is-equiv-htpy-eq-labeled-full-binary-tree :
    (T : full-binary-tree) (f g : labeling-full-binary-tree X T) →
    is-equiv (htpy-eq-labeled-full-binary-tree T f g)
  is-equiv-htpy-eq-labeled-full-binary-tree T f =
    fundamental-theorem-id
    ( is-torsorial-htpy-labeled-full-binary-tree T f)
    ( htpy-eq-labeled-full-binary-tree T f)

  is-equiv-Eq-eq-labeled-full-binary-tree :
    (U V : labeled-full-binary-tree X) →
    is-equiv (Eq-eq-labeled-full-binary-tree U V)
  is-equiv-Eq-eq-labeled-full-binary-tree (U , f) =
    structure-identity-principle
    ( λ {V} g → htpy-labeled-full-binary-tree (U , f) (V , g))
    ( refl-Eq-full-binary-tree U)
    ( refl-htpy-labeled-full-binary-tree (U , f))
    ( Eq-eq-labeled-full-binary-tree (U , f))
    ( λ _ → is-equiv-Eq-eq-full-binary-tree)
    ( is-equiv-htpy-eq-labeled-full-binary-tree U f)

  equiv-Eq-eq-labeled-full-binary-tree :
    (U V : labeled-full-binary-tree X) →
    (U ＝ V) ≃ Eq-labeled-full-binary-tree U V
  pr1 (equiv-Eq-eq-labeled-full-binary-tree U V) =
    Eq-eq-labeled-full-binary-tree U V
  pr2 (equiv-Eq-eq-labeled-full-binary-tree U V) =
    is-equiv-Eq-eq-labeled-full-binary-tree U V

  eq-Eq-labeled-full-binary-tree :
    (U V : labeled-full-binary-tree X) →
    Eq-labeled-full-binary-tree U V → U ＝ V
  eq-Eq-labeled-full-binary-tree U V =
    map-inv-equiv (equiv-Eq-eq-labeled-full-binary-tree U V)

  compute-Eq-eq-labeled-full-binary-tree :
    (U : labeled-full-binary-tree X) →
    Eq-eq-labeled-full-binary-tree U U refl ＝
    refl-Eq-labeled-full-binary-tree U
  compute-Eq-eq-labeled-full-binary-tree _ = refl
```
