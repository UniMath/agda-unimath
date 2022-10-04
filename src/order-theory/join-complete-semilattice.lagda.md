# join-complete-semilattice 

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.join-complete-semilattice where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.propositions using
  ( Prop; is-prop; type-Prop; is-prop-type-Prop; all-elements-equal;
    is-prop-all-elements-equal; prod-Prop; Π-Prop; function-Prop)
open import foundation.subtypes using (eq-type-subtype)
open import foundation.universe-levels
open import foundation.identity-types
open import foundation.sets

open import order-theory.posets
open import order-theory.least-upper-bounds-posets
open import order-theory.join-semilattices

```

## Idea
A join complete semilattice is a poset in which every family of elements has a least upperbound.
For full generality we will consider 3 different universe levels: one for the underlying type, one for
the order relation and one for the indexing type.

## Definitions

### Order theoretic join complete semilattices

```agda
module _
  {l1 l2 : Level} (l3 : Level) (P : Poset l1 l2) 
  where
  
  is-join-complete-semilattice-poset-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3) 
  is-join-complete-semilattice-poset-Prop =
    Π-Prop
      (UU l3)
      (λ I →
        Π-Prop
          ( I → element-Poset P )
          ( λ f → has-least-upper-bound-family-poset-Prop P f))

  is-join-complete-semilattice-Poset : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-join-complete-semilattice-Poset = type-Prop is-join-complete-semilattice-poset-Prop

  is-prop-is-join-complete-semilattice-Poset : is-prop is-join-complete-semilattice-Poset  
  is-prop-is-join-complete-semilattice-Poset = is-prop-type-Prop is-join-complete-semilattice-poset-Prop 

Join-Complete-Semilattice : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Join-Complete-Semilattice l1 l2 l3 = Σ (Poset l1 l2) (λ P → is-join-complete-semilattice-Poset l3 P)

```

We now develop the tools that allow us to work with the components of a join complete semilattice.

```agda

module _
  {l1 l2 l3 : Level} (A : Join-Complete-Semilattice l1 l2 l3)
  where

  poset-Join-Complete-Semilattice : Poset l1 l2
  poset-Join-Complete-Semilattice = pr1 A

  element-Join-Complete-Semilattice : UU l1    {- could we use carrier instead of element? -}
  element-Join-Complete-Semilattice = element-Poset poset-Join-Complete-Semilattice

  leq-join-complete-semilattice-Prop : (x y : element-Join-Complete-Semilattice) → Prop l2
  leq-join-complete-semilattice-Prop = leq-poset-Prop poset-Join-Complete-Semilattice

  leq-Join-Complete-Semilattice : (x y : element-Join-Complete-Semilattice) → UU l2
  leq-Join-Complete-Semilattice = leq-Poset poset-Join-Complete-Semilattice

  is-prop-leq-Join-Complete-Semilattice :
    (x y : element-Join-Complete-Semilattice) → is-prop (leq-Join-Complete-Semilattice x y)
  is-prop-leq-Join-Complete-Semilattice = is-prop-leq-Poset poset-Join-Complete-Semilattice

  refl-leq-Join-Complete-Semilattice :
    (x : element-Join-Complete-Semilattice) → leq-Join-Complete-Semilattice x x
  refl-leq-Join-Complete-Semilattice = refl-leq-Poset poset-Join-Complete-Semilattice

  antisymmetric-leq-Join-Complete-Semilattice :
    (x y : element-Join-Complete-Semilattice) →
    leq-Join-Complete-Semilattice x y → leq-Join-Complete-Semilattice y x → x ＝ y
  antisymmetric-leq-Join-Complete-Semilattice =
    antisymmetric-leq-Poset poset-Join-Complete-Semilattice

  transitive-leq-Join-Complete-Semilattice :
    (x y z : element-Join-Complete-Semilattice) →
    leq-Join-Complete-Semilattice y z → leq-Join-Complete-Semilattice x y →
    leq-Join-Complete-Semilattice x z
  transitive-leq-Join-Complete-Semilattice = transitive-leq-Poset poset-Join-Complete-Semilattice

  is-set-element-Join-Complete-Semilattice : is-set element-Join-Complete-Semilattice
  is-set-element-Join-Complete-Semilattice = is-set-element-Poset poset-Join-Complete-Semilattice

  element-join-complete-semilattice-Set : Set l1
  element-join-complete-semilattice-Set = element-poset-Set poset-Join-Complete-Semilattice

  is-join-complete-semilattice-Join-Complete-Semilattice :
    is-join-complete-semilattice-Poset l3 poset-Join-Complete-Semilattice 
  is-join-complete-semilattice-Join-Complete-Semilattice = pr2 A

  join-complete-semilattice-Join-Complete-Semilattice : Join-Complete-Semilattice l1 l2 l3
  pr1 join-complete-semilattice-Join-Complete-Semilattice = poset-Join-Complete-Semilattice
  pr2 join-complete-semilattice-Join-Complete-Semilattice = is-join-complete-semilattice-Join-Complete-Semilattice

  join-Join-Complete-Semilattice :
    (I : UU l3) → (I → element-Join-Complete-Semilattice) → element-Join-Complete-Semilattice
  join-Join-Complete-Semilattice I f = pr1 (is-join-complete-semilattice-Join-Complete-Semilattice I f)

  is-least-upper-bound-family-join-Join-Complete-Semilattice :
    (I : UU l3) → (f : I → element-Join-Complete-Semilattice) →
    is-least-upper-bound-family-Poset poset-Join-Complete-Semilattice f
      (join-Join-Complete-Semilattice I f)
  is-least-upper-bound-family-join-Join-Complete-Semilattice I f = pr2 (is-join-complete-semilattice-Join-Complete-Semilattice I f)

```

