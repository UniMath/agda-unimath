---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module the-circle.cyclic-types where

open import the-circle.infinite-cyclic-types public

Fin-Endo : ℕ → Endo lzero
pr1 (Fin-Endo k) = Fin k
pr2 (Fin-Endo k) = succ-Fin

Cyclic : (l : Level) → ℕ → UU (lsuc l)
Cyclic l zero-ℕ = Infinite-Cyclic l
Cyclic l (succ-ℕ k) = Σ (Endo l) (mere-equiv-Endo (Fin-Endo (succ-ℕ k)))

Fin-Cyclic : (k : ℕ) → Cyclic lzero (succ-ℕ k)
pr1 (Fin-Cyclic k) = Fin-Endo (succ-ℕ k)
pr2 (Fin-Cyclic k) = refl-mere-equiv-Endo (Fin-Endo (succ-ℕ k))

module _
  {l : Level}
  where

  endo-Cyclic : (k : ℕ) → Cyclic l k → Endo l
  endo-Cyclic zero-ℕ = pr1
  endo-Cyclic (succ-ℕ k) = pr1
  
  type-Cyclic : (k : ℕ) → Cyclic l k → UU l
  type-Cyclic zero-ℕ = type-Endo ∘ endo-Cyclic zero-ℕ
  type-Cyclic (succ-ℕ k) = type-Endo ∘ endo-Cyclic (succ-ℕ k)
  
  endomorphism-Cyclic :
    (k : ℕ) (X : Cyclic l k) → type-Cyclic k X → type-Cyclic k X
  endomorphism-Cyclic zero-ℕ X = endomorphism-Endo (endo-Cyclic zero-ℕ X)
  endomorphism-Cyclic (succ-ℕ k) X =
    endomorphism-Endo (endo-Cyclic (succ-ℕ k) X)

equiv-Cyclic :
  {l1  l2 : Level} (k : ℕ) (X : Cyclic l1 k) (Y : Cyclic l2 k) → UU (l1 ⊔ l2)
equiv-Cyclic k X Y = equiv-Endo (endo-Cyclic k X) (endo-Cyclic k Y)
                                                             
id-equiv-Cyclic : {l1 : Level} (k : ℕ) (X : Cyclic l1 k) → equiv-Cyclic k X X
id-equiv-Cyclic k X = id-equiv-Endo (endo-Cyclic k X)
                                                 
equiv-eq-Cyclic :
  {l1 : Level} (k : ℕ) (X Y : Cyclic l1 k) → Id X Y → equiv-Cyclic k X Y
equiv-eq-Cyclic k X .X refl = id-equiv-Cyclic k X
    
is-contr-total-equiv-Cyclic :
  {l1 : Level} (k : ℕ) (X : Cyclic l1 k) →
  is-contr (Σ (Cyclic l1 k) (equiv-Cyclic k X))
is-contr-total-equiv-Cyclic zero-ℕ X = is-contr-total-equiv-Infinite-Cyclic X
is-contr-total-equiv-Cyclic (succ-ℕ k) X =
  is-contr-total-Eq-substructure
    ( is-contr-total-equiv-Endo (endo-Cyclic (succ-ℕ k) X))
    ( λ Y → is-prop-type-trunc-Prop)
    ( endo-Cyclic (succ-ℕ k) X)
    ( id-equiv-Endo (endo-Cyclic (succ-ℕ k) X))
    ( pr2 X)

is-equiv-equiv-eq-Cyclic :
  {l1 : Level} (k : ℕ) (X Y : Cyclic l1 k) → is-equiv (equiv-eq-Cyclic k X Y)
is-equiv-equiv-eq-Cyclic k X =
  fundamental-theorem-id X
    ( id-equiv-Cyclic k X)
    ( is-contr-total-equiv-Cyclic k X)
    ( equiv-eq-Cyclic k X)

extensionality-Cyclic :
  {l1 : Level} (k : ℕ) (X Y : Cyclic l1 k) → Id X Y ≃ equiv-Cyclic k X Y
pr1 (extensionality-Cyclic k X Y) = equiv-eq-Cyclic k X Y
pr2 (extensionality-Cyclic k X Y) = is-equiv-equiv-eq-Cyclic k X Y

eq-equiv-Cyclic :
  {l1 : Level} (k : ℕ) (X Y : Cyclic l1 k) → equiv-Cyclic k X Y → Id X Y
eq-equiv-Cyclic k X Y =
  map-inv-is-equiv (is-equiv-equiv-eq-Cyclic k X Y)

comp-equiv-Cyclic :
  {l1 l2 l3 : Level} (k : ℕ) (X : Cyclic l1 k) (Y : Cyclic l2 k)
  (Z : Cyclic l3 k) →
  equiv-Cyclic k Y Z → equiv-Cyclic k X Y → equiv-Cyclic k X Z
comp-equiv-Cyclic k X Y Z =
  {!comp-equiv-Endo ? ? ?!}

```
