# Title: Infinite distributive law 

```agda

module order-theory.infinite-distributive-law where

open import foundation.cartesian-product-types 
open import foundation.dependent-pair-types 
open import foundation.propositions 
open import foundation.subtypes 
open import foundation.universe-levels
open import foundation.identity-types
open import foundation.sets

open import order-theory.posets
open import order-theory.least-upper-bounds-posets
open import order-theory.join-complete-semilattice
open import order-theory.meet-semilattices

```

## Idea
Let A be a poset that has all binary meets and arbitrary joins. The infinite distributive law states
for all a : A and for all families b : I → A the following identity holds
                  a ∧ (‌‌‌⋁ᵢ bᵢ) ＝ ⋁ᵢ (a ∧ bᵢ)
Note: One could inquire about the dual infinite distributive law but it is not needed at this time.


```agda

module _
  {l1 l2 : Level} (l3 : Level) (P : Poset l1 l2)
  where

  is-meet-semilattice-and-join-complete-semilattice-poset-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-meet-semilattice-and-join-complete-semilattice-poset-Prop =
    prod-Prop (is-meet-semilattice-poset-Prop P) (is-join-complete-semilattice-poset-Prop l3 P)

  is-meet-semilattice-and-join-complete-semilattice-Poset : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-meet-semilattice-and-join-complete-semilattice-Poset = type-Prop is-meet-semilattice-and-join-complete-semilattice-poset-Prop

  is-prop-is-meet-semilattice-and-join-complete-semilattice-Poset : is-prop is-meet-semilattice-and-join-complete-semilattice-Poset
  is-prop-is-meet-semilattice-and-join-complete-semilattice-Poset = is-prop-type-Prop is-meet-semilattice-and-join-complete-semilattice-poset-Prop

Meet-Semilattice-and-Join-Complete-Semilattice : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Meet-Semilattice-and-Join-Complete-Semilattice l1 l2 l3 =
  Σ (Poset l1 l2) (λ P → is-meet-semilattice-and-join-complete-semilattice-Poset l3 P)

```

## We need to provide the appropriate components to state the infinite distributive law "more?" easiliy.

```agda

module _
  {l1 l2 l3 : Level} (A : Meet-Semilattice-and-Join-Complete-Semilattice l1 l2 l3)
  where

  poset-Meet-Semilattice-and-Join-Complete-Semilattice : Poset l1 l2
  poset-Meet-Semilattice-and-Join-Complete-Semilattice = pr1 A

  element-Meet-Semilattice-and-Join-Complete-Semilattice : UU l1
  element-Meet-Semilattice-and-Join-Complete-Semilattice =
    element-Poset poset-Meet-Semilattice-and-Join-Complete-Semilattice

  {- I should fill this in later with all the things...
  right now I want to get to the meet and join operations
  so I can state the infinite distributive law. -}

  is-meet-semilattice-Meet-Semilattice-and-Join-Complete-Semilattice :
    is-meet-semilattice-Poset poset-Meet-Semilattice-and-Join-Complete-Semilattice
  is-meet-semilattice-Meet-Semilattice-and-Join-Complete-Semilattice = pr1 (pr2 A)

  is-join-complete-semilattice-Meet-Semilattice-and-Join-Complete-Semilattice :
    is-join-complete-semilattice-Poset l3 poset-Meet-Semilattice-and-Join-Complete-Semilattice
  is-join-complete-semilattice-Meet-Semilattice-and-Join-Complete-Semilattice = pr2 (pr2 A)

  meet-semilattice-and-join-complete-semilattice-Meet-Semilattice-and-Join-Complete-Semilattice :
    Meet-Semilattice-and-Join-Complete-Semilattice l1 l2 l3
  pr1 meet-semilattice-and-join-complete-semilattice-Meet-Semilattice-and-Join-Complete-Semilattice =
    poset-Meet-Semilattice-and-Join-Complete-Semilattice
  pr1 (pr2 meet-semilattice-and-join-complete-semilattice-Meet-Semilattice-and-Join-Complete-Semilattice) =
    is-meet-semilattice-Meet-Semilattice-and-Join-Complete-Semilattice
  pr2 (pr2 meet-semilattice-and-join-complete-semilattice-Meet-Semilattice-and-Join-Complete-Semilattice) =
    is-join-complete-semilattice-Meet-Semilattice-and-Join-Complete-Semilattice

  meet-Meet-Semilattice-and-Join-Complete-Semilattice :
    (x y : element-Meet-Semilattice-and-Join-Complete-Semilattice) →
    element-Meet-Semilattice-and-Join-Complete-Semilattice
  meet-Meet-Semilattice-and-Join-Complete-Semilattice x y = pr1 (is-meet-semilattice-Meet-Semilattice-and-Join-Complete-Semilattice x y)

  join-Meet-Semilattice-and-Join-Complete-Semilattice :
    (I : UU l3) → (I → element-Meet-Semilattice-and-Join-Complete-Semilattice) →
    element-Meet-Semilattice-and-Join-Complete-Semilattice
  join-Meet-Semilattice-and-Join-Complete-Semilattice I f = pr1 (is-join-complete-semilattice-Meet-Semilattice-and-Join-Complete-Semilattice I f)

```

## We now state the infinite distributive law

```agda

infinite-distributive-law : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
infinite-distributive-law l1 l2 l3 =
  (A : Meet-Semilattice-and-Join-Complete-Semilattice l1 l2 l3)
  (a : element-Meet-Semilattice-and-Join-Complete-Semilattice A) → (I : UU l3) →
  (b : I → element-Meet-Semilattice-and-Join-Complete-Semilattice A) →
  (meet-Meet-Semilattice-and-Join-Complete-Semilattice A a (join-Meet-Semilattice-and-Join-Complete-Semilattice A I b) ＝
  join-Meet-Semilattice-and-Join-Complete-Semilattice A I (λ i → (meet-Meet-Semilattice-and-Join-Complete-Semilattice A a (b i))))

{- this notation is note easy on the eye, but recall, in more familiar notation the identity expressed here is:
                                a ∧ (‌‌‌⋁ᵢ bᵢ) ＝ ⋁ᵢ (a ∧ bᵢ)
-}

{- Show that the identity is a prop -}

```
