# Inequality on the MacNeille real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.inequality-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders

open import real-numbers.inequality-lower-dedekind-real-numbers
open import real-numbers.inequality-upper-dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "standard ordering" Disambiguation="MacNeille real numbers" Agda=leq-macneille-ℝ}}
on the [MacNeille real numbers](real-numbers.macneille-real-numbers.md) is the
nLab order on open Dedekind-MacNeille cuts:

- `Lx ⊆ Ly` on lower cuts, and
- `Uy ⊆ Ux` on upper cuts.

## Definitions

```agda
module _
  {l1 l2 : Level}
  (x : macneille-ℝ l1)
  (y : macneille-ℝ l2)
  where

  leq-lower-prop-macneille-ℝ : Prop (l1 ⊔ l2)
  leq-lower-prop-macneille-ℝ =
    leq-lower-ℝ-Prop (lower-macneille-ℝ x) (lower-macneille-ℝ y)

  leq-lower-macneille-ℝ : UU (l1 ⊔ l2)
  leq-lower-macneille-ℝ = type-Prop leq-lower-prop-macneille-ℝ

  is-prop-leq-lower-macneille-ℝ : is-prop leq-lower-macneille-ℝ
  is-prop-leq-lower-macneille-ℝ = is-prop-type-Prop leq-lower-prop-macneille-ℝ

  leq-upper-prop-macneille-ℝ : Prop (l1 ⊔ l2)
  leq-upper-prop-macneille-ℝ =
    leq-upper-ℝ-Prop (upper-macneille-ℝ x) (upper-macneille-ℝ y)

  leq-upper-macneille-ℝ : UU (l1 ⊔ l2)
  leq-upper-macneille-ℝ = type-Prop leq-upper-prop-macneille-ℝ

  is-prop-leq-upper-macneille-ℝ : is-prop leq-upper-macneille-ℝ
  is-prop-leq-upper-macneille-ℝ = is-prop-type-Prop leq-upper-prop-macneille-ℝ

  leq-macneille-ℝ : UU (l1 ⊔ l2)
  leq-macneille-ℝ = leq-lower-macneille-ℝ × leq-upper-macneille-ℝ

  is-prop-leq-macneille-ℝ : is-prop leq-macneille-ℝ
  is-prop-leq-macneille-ℝ =
    is-prop-product
      is-prop-leq-lower-macneille-ℝ
      is-prop-leq-upper-macneille-ℝ

  leq-prop-macneille-ℝ : Prop (l1 ⊔ l2)
  leq-prop-macneille-ℝ = leq-macneille-ℝ , is-prop-leq-macneille-ℝ
```

## Properties

### Lower- and upper-cut formulations are equivalent

```agda
module _
  {l1 l2 : Level} (x : macneille-ℝ l1) (y : macneille-ℝ l2)
  where

  leq-upper-leq-lower-macneille-ℝ :
    leq-lower-macneille-ℝ x y →
    leq-upper-macneille-ℝ x y
  leq-upper-leq-lower-macneille-ℝ lx⊆ly q y<q =
    elim-exists
      ( cut-upper-ℝ (upper-macneille-ℝ x) q)
      ( λ p (p<q , p∉Ly) →
        backward-implication
          ( is-open-upper-complement-lower-cut-macneille-ℝ x q)
          ( intro-exists p (p<q , p∉Ly ∘ lx⊆ly p)))
      ( forward-implication
        ( is-open-upper-complement-lower-cut-macneille-ℝ y q)
        y<q)

  leq-lower-leq-upper-macneille-ℝ :
    leq-upper-macneille-ℝ x y →
    leq-lower-macneille-ℝ x y
  leq-lower-leq-upper-macneille-ℝ uy⊆ux p p<x =
    elim-exists
      ( cut-lower-ℝ (lower-macneille-ℝ y) p)
      ( λ q (p<q , q∉Ux) →
        backward-implication
          ( is-open-lower-complement-upper-cut-macneille-ℝ y p)
          ( intro-exists q (p<q , q∉Ux ∘ uy⊆ux q)))
      ( forward-implication
        ( is-open-lower-complement-upper-cut-macneille-ℝ x p)
        p<x)

  leq-macneille-leq-lower-macneille-ℝ :
    leq-lower-macneille-ℝ x y →
    leq-macneille-ℝ x y
  leq-macneille-leq-lower-macneille-ℝ lx⊆ly =
    lx⊆ly , leq-upper-leq-lower-macneille-ℝ lx⊆ly

  leq-macneille-leq-upper-macneille-ℝ :
    leq-upper-macneille-ℝ x y →
    leq-macneille-ℝ x y
  leq-macneille-leq-upper-macneille-ℝ uy⊆ux =
    leq-lower-leq-upper-macneille-ℝ uy⊆ux , uy⊆ux
```

### Inequality on MacNeille reals is reflexive

```agda
refl-leq-macneille-ℝ :
  {l : Level} (x : macneille-ℝ l) → leq-macneille-ℝ x x
refl-leq-macneille-ℝ x =
  refl-leq-lower-ℝ (lower-macneille-ℝ x) ,
  refl-leq-upper-ℝ (upper-macneille-ℝ x)
```

### Inequality on MacNeille reals is transitive

```agda
transitive-leq-macneille-ℝ :
  {l1 l2 l3 : Level} →
  (x : macneille-ℝ l1) (y : macneille-ℝ l2) (z : macneille-ℝ l3) →
  leq-macneille-ℝ y z → leq-macneille-ℝ x y → leq-macneille-ℝ x z
transitive-leq-macneille-ℝ x y z y≤z x≤y =
  ( transitive-leq-lower-ℝ
      ( lower-macneille-ℝ x)
      ( lower-macneille-ℝ y)
      ( lower-macneille-ℝ z)
      ( pr1 y≤z)
      ( pr1 x≤y) ,
    transitive-leq-upper-ℝ
      ( upper-macneille-ℝ x)
      ( upper-macneille-ℝ y)
      ( upper-macneille-ℝ z)
      ( pr2 y≤z)
      ( pr2 x≤y))
```

### Inequality on MacNeille reals is antisymmetric

```agda
antisymmetric-leq-macneille-ℝ :
  {l : Level} (x y : macneille-ℝ l) →
  leq-macneille-ℝ x y → leq-macneille-ℝ y x → x ＝ y
antisymmetric-leq-macneille-ℝ x y x≤y y≤x =
  eq-macneille-ℝ
    ( x)
    ( y)
    ( antisymmetric-leq-lower-ℝ
      ( lower-macneille-ℝ x)
      ( lower-macneille-ℝ y)
      ( pr1 x≤y)
      ( pr1 y≤x))
    ( antisymmetric-leq-upper-ℝ
      ( upper-macneille-ℝ x)
      ( upper-macneille-ℝ y)
      ( pr2 x≤y)
      ( pr2 y≤x))
```

### Inequality on MacNeille reals is a large poset

```agda
large-preorder-macneille-ℝ : Large-Preorder lsuc (_⊔_)
large-preorder-macneille-ℝ =
  λ where
  .type-Large-Preorder → macneille-ℝ
  .leq-prop-Large-Preorder → leq-prop-macneille-ℝ
  .refl-leq-Large-Preorder → refl-leq-macneille-ℝ
  .transitive-leq-Large-Preorder → transitive-leq-macneille-ℝ

large-poset-macneille-ℝ : Large-Poset lsuc (_⊔_)
large-poset-macneille-ℝ =
  λ where
  .large-preorder-Large-Poset → large-preorder-macneille-ℝ
  .antisymmetric-leq-Large-Poset → antisymmetric-leq-macneille-ℝ
```
