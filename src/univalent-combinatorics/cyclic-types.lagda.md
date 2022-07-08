---
title: Cyclic types
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.cyclic-types where

open import elementary-number-theory.addition-integers using
  ( left-unit-law-add-ℤ)
open import elementary-number-theory.groups-of-modular-arithmetic using
  ( ℤ-Mod-Group)
open import elementary-number-theory.integers using (ℤ; succ-ℤ; zero-ℤ)
open import elementary-number-theory.modular-arithmetic using
  ( ℤ-Mod; succ-ℤ-Mod; is-set-ℤ-Mod; zero-ℤ-Mod; equiv-add-ℤ-Mod';
    left-successor-law-add-ℤ-Mod; pred-ℤ-Mod; isretr-pred-ℤ-Mod;
    issec-pred-ℤ-Mod; add-ℤ-Mod; mod-ℤ; add-ℤ-Mod'; mod-neg-one-ℤ;
    is-add-neg-one-pred-ℤ-Mod; mod-zero-ℤ; preserves-predecessor-mod-ℤ;
    left-predecessor-law-add-ℤ-Mod; left-unit-law-add-ℤ-Mod; ap-add-ℤ-Mod;
    mod-one-ℤ; is-add-one-succ-ℤ-Mod; preserves-successor-mod-ℤ;
    issec-int-ℤ-Mod; int-ℤ-Mod; ℤ-Mod-Endo)
open import elementary-number-theory.modular-arithmetic-standard-finite-types
  using (left-unit-law-add-Fin)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.commuting-squares using
  ( coherence-square; coherence-square-comp-horizontal;
    coherence-square-inv-horizontal)
open import foundation.connected-types using
  ( is-path-connected; is-path-connected-mere-eq)
open import foundation.contractible-types using
  ( is-contr; is-contr-equiv; is-contr-equiv'; is-contr-Π)
open import foundation.coproduct-types using (inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _≃_; map-equiv; id-equiv; is-equiv; map-inv-is-equiv; _∘e_; inv-equiv;
    map-inv-equiv; is-property-is-equiv; isretr-map-inv-equiv;
    issec-map-inv-equiv; is-equiv-Prop; is-equiv-has-inverse)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot; equiv-Σ)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using
  ( refl-htpy; _~_; is-contr-total-htpy; _·r_; _∙h_; _·l_; inv-htpy;
    right-unit-htpy; equiv-concat-htpy'; is-contr-total-htpy')
open import foundation.identity-types using
  ( Id; inv; right-unit; _∙_; ap-id; ap; refl)
open import foundation.mere-equality using (mere-eq; mere-eq-Prop)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; unit-trunc-Prop; is-prop-type-trunc-Prop;
    apply-universal-property-trunc-Prop)
open import foundation.sets using
  ( is-set; is-set-Prop; is-set-equiv'; is-set-equiv; UU-Set)
open import foundation.structure-identity-principle using
  ( is-contr-total-Eq-structure)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.type-arithmetic-dependent-pair-types using
  ( equiv-right-swap-Σ; right-unit-law-Σ-is-contr)
open import foundation.unit-type using (star)
open import foundation.univalence using (is-contr-total-equiv)
open import foundation.universe-levels using (Level; UU; lsuc; lzero; _⊔_)

open import group-theory.groups using (Group)
open import group-theory.isomorphisms-groups using
  ( type-iso-Group; iso-equiv-Group; equiv-Group)

open import structured-types.equivalences-types-equipped-with-endomorphisms
open import structured-types.mere-equivalences-types-equipped-with-endomorphisms
open import structured-types.morphisms-types-equipped-with-endomorphisms
open import structured-types.pointed-types using (Pointed-Type)
open import structured-types.types-equipped-with-endomorphisms

open import synthetic-homotopy-theory.groups-of-loops-in-1-types using
  ( loop-space-Group)
open import synthetic-homotopy-theory.loop-spaces using (type-Ω)

open import univalent-combinatorics.standard-finite-types using
  ( Fin; succ-Fin; Fin-Endo)
```

## Idea

A cyclic type is a type `X` equipped with an endomorphism `f : X → X` such that the pair `(X, f)` is merely equivalent to the pair `(ℤ-Mod k, +1)` for some `k : ℕ`.

## Definitions

### The type of cyclic types of a given order

```agda
is-cyclic-Endo : {l : Level} → ℕ → Endo l → UU l
is-cyclic-Endo k X = mere-equiv-Endo (ℤ-Mod-Endo k) X

Cyclic-Type : (l : Level) → ℕ → UU (lsuc l)
Cyclic-Type l k = Σ (Endo l) (is-cyclic-Endo k)

module _
  {l : Level} (k : ℕ) (X : Cyclic-Type l k)
  where

  endo-Cyclic-Type : Endo l
  endo-Cyclic-Type = pr1 X

  type-Cyclic-Type : UU l
  type-Cyclic-Type = type-Endo endo-Cyclic-Type

  endomorphism-Cyclic-Type : type-Cyclic-Type → type-Cyclic-Type
  endomorphism-Cyclic-Type = endomorphism-Endo endo-Cyclic-Type

  mere-equiv-endo-Cyclic-Type : mere-equiv-Endo (ℤ-Mod-Endo k) endo-Cyclic-Type
  mere-equiv-endo-Cyclic-Type = pr2 X

  is-set-type-Cyclic-Type : is-set type-Cyclic-Type
  is-set-type-Cyclic-Type =
    apply-universal-property-trunc-Prop
      ( mere-equiv-endo-Cyclic-Type)
      ( is-set-Prop type-Cyclic-Type)
      ( λ e →
        is-set-equiv'
          ( ℤ-Mod k)
          ( equiv-equiv-Endo (ℤ-Mod-Endo k) endo-Cyclic-Type e)
          ( is-set-ℤ-Mod k))

  set-Cyclic-Type : UU-Set l
  pr1 set-Cyclic-Type = type-Cyclic-Type
  pr2 set-Cyclic-Type = is-set-type-Cyclic-Type
```

### Cyclic-Type structure on a type

```agda
cyclic-structure : {l : Level} → ℕ → UU l → UU l
cyclic-structure k X = Σ (X → X) (λ f → is-cyclic-Endo k (pair X f))

cyclic-type-cyclic-structure :
  {l : Level} (k : ℕ) {X : UU l} → cyclic-structure k X → Cyclic-Type l k
pr1 (pr1 (cyclic-type-cyclic-structure k {X} c)) = X
pr2 (pr1 (cyclic-type-cyclic-structure k c)) = pr1 c
pr2 (cyclic-type-cyclic-structure k c) = pr2 c
```

### The standard cyclic types

```agda
ℤ-Mod-Cyclic-Type : (k : ℕ) → Cyclic-Type lzero k
pr1 (ℤ-Mod-Cyclic-Type k) = ℤ-Mod-Endo k
pr2 (ℤ-Mod-Cyclic-Type k) = refl-mere-equiv-Endo (ℤ-Mod-Endo k)

Fin-Cyclic-Type : (k : ℕ) → Cyclic-Type lzero (succ-ℕ k)
Fin-Cyclic-Type k = ℤ-Mod-Cyclic-Type (succ-ℕ k)

Cyclic-Type-Pointed-Type : (k : ℕ) → Pointed-Type (lsuc lzero)
pr1 (Cyclic-Type-Pointed-Type k) = Cyclic-Type lzero k
pr2 (Cyclic-Type-Pointed-Type k) = ℤ-Mod-Cyclic-Type k
```

### Equivalences of cyclic types

```agda
module _
  {l1 l2 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  where
  
  equiv-Cyclic-Type : UU (l1 ⊔ l2)
  equiv-Cyclic-Type = equiv-Endo (endo-Cyclic-Type k X) (endo-Cyclic-Type k Y)

  equiv-equiv-Cyclic-Type :
    equiv-Cyclic-Type → type-Cyclic-Type k X ≃ type-Cyclic-Type k Y
  equiv-equiv-Cyclic-Type =
    equiv-equiv-Endo (endo-Cyclic-Type k X) (endo-Cyclic-Type k Y)

  map-equiv-Cyclic-Type :
    equiv-Cyclic-Type → type-Cyclic-Type k X → type-Cyclic-Type k Y
  map-equiv-Cyclic-Type e =
    map-equiv-Endo (endo-Cyclic-Type k X) (endo-Cyclic-Type k Y) e

  coherence-square-equiv-Cyclic-Type :
    (e : equiv-Cyclic-Type) →
    coherence-square
      ( map-equiv-Cyclic-Type e)
      ( endomorphism-Cyclic-Type k X)
      ( endomorphism-Cyclic-Type k Y)
      ( map-equiv-Cyclic-Type e)
  coherence-square-equiv-Cyclic-Type e = pr2 e

module _
  {l : Level} (k : ℕ) (X : Cyclic-Type l k)
  where

  id-equiv-Cyclic-Type : equiv-Cyclic-Type k X X
  id-equiv-Cyclic-Type = id-equiv-Endo (endo-Cyclic-Type k X)
                                                 
  equiv-eq-Cyclic-Type :
    (Y : Cyclic-Type l k) → Id X Y → equiv-Cyclic-Type k X Y
  equiv-eq-Cyclic-Type .X refl = id-equiv-Cyclic-Type

is-contr-total-equiv-Cyclic-Type :
  {l1 : Level} (k : ℕ) (X : Cyclic-Type l1 k) →
  is-contr (Σ (Cyclic-Type l1 k) (equiv-Cyclic-Type k X))
is-contr-total-equiv-Cyclic-Type k X =
  is-contr-total-Eq-subtype
    ( is-contr-total-equiv-Endo (endo-Cyclic-Type k X))
    ( λ Y → is-prop-type-trunc-Prop)
    ( endo-Cyclic-Type k X)
    ( id-equiv-Endo (endo-Cyclic-Type k X))
    ( mere-equiv-endo-Cyclic-Type k X)

module _
  {l : Level} (k : ℕ) (X : Cyclic-Type l k)
  where
  
  is-equiv-equiv-eq-Cyclic-Type :
    (Y : Cyclic-Type l k) → is-equiv (equiv-eq-Cyclic-Type k X Y)
  is-equiv-equiv-eq-Cyclic-Type =
    fundamental-theorem-id X
      ( id-equiv-Cyclic-Type k X)
      ( is-contr-total-equiv-Cyclic-Type k X)
      ( equiv-eq-Cyclic-Type k X)

  extensionality-Cyclic-Type :
    (Y : Cyclic-Type l k) → Id X Y ≃ equiv-Cyclic-Type k X Y
  pr1 (extensionality-Cyclic-Type Y) = equiv-eq-Cyclic-Type k X Y
  pr2 (extensionality-Cyclic-Type Y) = is-equiv-equiv-eq-Cyclic-Type Y
  
  eq-equiv-Cyclic-Type :
    (Y : Cyclic-Type l k) → equiv-Cyclic-Type k X Y → Id X Y
  eq-equiv-Cyclic-Type Y = map-inv-is-equiv (is-equiv-equiv-eq-Cyclic-Type Y)
```

## Properties

```agda
module _
  {l1 l2 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  where

  htpy-equiv-Cyclic-Type : (e f : equiv-Cyclic-Type k X Y) → UU (l1 ⊔ l2)
  htpy-equiv-Cyclic-Type e f =
    map-equiv-Cyclic-Type k X Y e ~ map-equiv-Cyclic-Type k X Y f

  refl-htpy-equiv-Cyclic-Type :
    (e : equiv-Cyclic-Type k X Y) → htpy-equiv-Cyclic-Type e e
  refl-htpy-equiv-Cyclic-Type e = refl-htpy

  htpy-eq-equiv-Cyclic-Type :
    (e f : equiv-Cyclic-Type k X Y) → Id e f → htpy-equiv-Cyclic-Type e f
  htpy-eq-equiv-Cyclic-Type e .e refl = refl-htpy-equiv-Cyclic-Type e

  is-contr-total-htpy-equiv-Cyclic-Type :
    (e : equiv-Cyclic-Type k X Y) →
    is-contr (Σ (equiv-Cyclic-Type k X Y) (htpy-equiv-Cyclic-Type e))
  is-contr-total-htpy-equiv-Cyclic-Type e =
    is-contr-equiv'
      ( Σ ( equiv-Endo (endo-Cyclic-Type k X) (endo-Cyclic-Type k Y))
          ( htpy-equiv-Endo (endo-Cyclic-Type k X) (endo-Cyclic-Type k Y) e))
      ( equiv-tot
        ( λ f →
          right-unit-law-Σ-is-contr
            ( λ H →
              is-contr-Π
                ( λ x →
                  is-set-type-Cyclic-Type k Y
                  ( map-equiv-Cyclic-Type k X Y e
                    ( endomorphism-Cyclic-Type k X x))
                  ( endomorphism-Cyclic-Type k Y
                    ( map-equiv-Cyclic-Type k X Y f x))
                  ( ( H (endomorphism-Cyclic-Type k X x)) ∙
                    ( coherence-square-equiv-Cyclic-Type k X Y f x))
                  ( ( coherence-square-equiv-Cyclic-Type k X Y e x) ∙
                    ( ap (endomorphism-Cyclic-Type k Y) (H x)))))))
      ( is-contr-total-htpy-equiv-Endo
        ( endo-Cyclic-Type k X)
        ( endo-Cyclic-Type k Y)
        ( e))

  is-equiv-htpy-eq-equiv-Cyclic-Type :
    (e f : equiv-Cyclic-Type k X Y) → is-equiv (htpy-eq-equiv-Cyclic-Type e f)
  is-equiv-htpy-eq-equiv-Cyclic-Type e =
    fundamental-theorem-id e
      ( refl-htpy-equiv-Cyclic-Type e)
      ( is-contr-total-htpy-equiv-Cyclic-Type e)
      ( htpy-eq-equiv-Cyclic-Type e)

  extensionality-equiv-Cyclic-Type :
    (e f : equiv-Cyclic-Type k X Y) → Id e f ≃ htpy-equiv-Cyclic-Type e f
  pr1 (extensionality-equiv-Cyclic-Type e f) = htpy-eq-equiv-Cyclic-Type e f
  pr2 (extensionality-equiv-Cyclic-Type e f) =
    is-equiv-htpy-eq-equiv-Cyclic-Type e f

  eq-htpy-equiv-Cyclic-Type :
    (e f : equiv-Cyclic-Type k X Y) → htpy-equiv-Cyclic-Type e f → Id e f
  eq-htpy-equiv-Cyclic-Type e f =
    map-inv-equiv (extensionality-equiv-Cyclic-Type e f)

comp-equiv-Cyclic-Type :
  {l1 l2 l3 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  (Z : Cyclic-Type l3 k) →
  equiv-Cyclic-Type k Y Z → equiv-Cyclic-Type k X Y → equiv-Cyclic-Type k X Z
comp-equiv-Cyclic-Type k X Y Z =
  comp-equiv-Endo
    ( endo-Cyclic-Type k X)
    ( endo-Cyclic-Type k Y)
    ( endo-Cyclic-Type k Z)

inv-equiv-Cyclic-Type :
  {l1 l2 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k) →
  equiv-Cyclic-Type k X Y → equiv-Cyclic-Type k Y X
inv-equiv-Cyclic-Type k X Y =
  inv-equiv-Endo (endo-Cyclic-Type k X) (endo-Cyclic-Type k Y)

associative-comp-equiv-Cyclic-Type :
  {l1 l2 l3 l4 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  (Z : Cyclic-Type l3 k) (W : Cyclic-Type l4 k) (g : equiv-Cyclic-Type k Z W)
  (f : equiv-Cyclic-Type k Y Z) (e : equiv-Cyclic-Type k X Y) →
  Id ( comp-equiv-Cyclic-Type k X Y W (comp-equiv-Cyclic-Type k Y Z W g f) e)
     ( comp-equiv-Cyclic-Type k X Z W g (comp-equiv-Cyclic-Type k X Y Z f e))
associative-comp-equiv-Cyclic-Type k X Y Z W g f e =
  eq-htpy-equiv-Cyclic-Type k X W
    ( comp-equiv-Cyclic-Type k X Y W (comp-equiv-Cyclic-Type k Y Z W g f) e)
    ( comp-equiv-Cyclic-Type k X Z W g (comp-equiv-Cyclic-Type k X Y Z f e))
    ( refl-htpy)

module _
  {l1 l2 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  (e : equiv-Cyclic-Type k X Y)
  where
  
  left-unit-law-comp-equiv-Cyclic-Type :
    Id (comp-equiv-Cyclic-Type k X Y Y (id-equiv-Cyclic-Type k Y) e) e
  left-unit-law-comp-equiv-Cyclic-Type =
    eq-htpy-equiv-Cyclic-Type k X Y
      ( comp-equiv-Cyclic-Type k X Y Y (id-equiv-Cyclic-Type k Y) e)
      ( e)
      ( refl-htpy)

  right-unit-law-comp-equiv-Cyclic-Type :
    Id (comp-equiv-Cyclic-Type k X X Y e (id-equiv-Cyclic-Type k X)) e
  right-unit-law-comp-equiv-Cyclic-Type =
    eq-htpy-equiv-Cyclic-Type k X Y
      ( comp-equiv-Cyclic-Type k X X Y e (id-equiv-Cyclic-Type k X))
      ( e)
      ( refl-htpy)

  left-inverse-law-comp-equiv-Cyclic-Type :
    Id ( comp-equiv-Cyclic-Type k X Y X (inv-equiv-Cyclic-Type k X Y e) e)
       ( id-equiv-Cyclic-Type k X)
  left-inverse-law-comp-equiv-Cyclic-Type =
    eq-htpy-equiv-Cyclic-Type k X X
      ( comp-equiv-Cyclic-Type k X Y X (inv-equiv-Cyclic-Type k X Y e) e)
      ( id-equiv-Cyclic-Type k X)
      ( isretr-map-inv-equiv (equiv-equiv-Cyclic-Type k X Y e))

  right-inverse-law-comp-equiv-Cyclic-Type :
    Id ( comp-equiv-Cyclic-Type k Y X Y e (inv-equiv-Cyclic-Type k X Y e))
       ( id-equiv-Cyclic-Type k Y)
  right-inverse-law-comp-equiv-Cyclic-Type =
    eq-htpy-equiv-Cyclic-Type k Y Y
      ( comp-equiv-Cyclic-Type k Y X Y e (inv-equiv-Cyclic-Type k X Y e))
      ( id-equiv-Cyclic-Type k Y)
      ( issec-map-inv-equiv (equiv-equiv-Cyclic-Type k X Y e))

mere-eq-Cyclic-Type : {l : Level} (k : ℕ) (X Y : Cyclic-Type l k) → mere-eq X Y
mere-eq-Cyclic-Type k X Y =
  apply-universal-property-trunc-Prop
    ( mere-equiv-endo-Cyclic-Type k X)
    ( mere-eq-Prop X Y)
    ( λ e →
      apply-universal-property-trunc-Prop
        ( mere-equiv-endo-Cyclic-Type k Y)
        ( mere-eq-Prop X Y)
        ( λ f →
          unit-trunc-Prop
            ( eq-equiv-Cyclic-Type k X Y
              ( comp-equiv-Cyclic-Type k X (ℤ-Mod-Cyclic-Type k) Y f
                ( inv-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) X e)))))

is-path-connected-Cyclic-Type :
  (k : ℕ) → is-path-connected (Cyclic-Type lzero k)
is-path-connected-Cyclic-Type k =
  is-path-connected-mere-eq
    ( ℤ-Mod-Cyclic-Type k)
    ( mere-eq-Cyclic-Type k (ℤ-Mod-Cyclic-Type k))

Eq-Cyclic-Type : (k : ℕ) → Cyclic-Type lzero k → UU lzero
Eq-Cyclic-Type k X = type-Cyclic-Type k X

refl-Eq-Cyclic-Type : (k : ℕ) → Eq-Cyclic-Type k (ℤ-Mod-Cyclic-Type k)
refl-Eq-Cyclic-Type k = zero-ℤ-Mod k

Eq-equiv-Cyclic-Type :
  (k : ℕ) (X : Cyclic-Type lzero k) →
  equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) X → Eq-Cyclic-Type k X
Eq-equiv-Cyclic-Type k X e =
  map-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) X e (zero-ℤ-Mod k)

equiv-Eq-Cyclic-Type :
  (k : ℕ) → Eq-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) →
  equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k)
pr1 (equiv-Eq-Cyclic-Type k x) = equiv-add-ℤ-Mod' k x
pr2 (equiv-Eq-Cyclic-Type k x) y = left-successor-law-add-ℤ-Mod k y x

issec-equiv-Eq-Cyclic-Type :
  (k : ℕ) →
  (Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) ∘ equiv-Eq-Cyclic-Type k) ~ id
issec-equiv-Eq-Cyclic-Type zero-ℕ x = left-unit-law-add-ℤ x
issec-equiv-Eq-Cyclic-Type (succ-ℕ k) x = left-unit-law-add-Fin k x

preserves-pred-preserves-succ-map-ℤ-Mod :
  (k : ℕ) (f : ℤ-Mod k → ℤ-Mod k) →
  (f ∘ succ-ℤ-Mod k) ~ (succ-ℤ-Mod k ∘ f) →
  (f ∘ pred-ℤ-Mod k) ~ (pred-ℤ-Mod k ∘ f)
preserves-pred-preserves-succ-map-ℤ-Mod k f H x =
  ( inv (isretr-pred-ℤ-Mod k (f (pred-ℤ-Mod k x)))) ∙
  ( ap
    ( pred-ℤ-Mod k)
    ( ( inv (H (pred-ℤ-Mod k x))) ∙
      ( ap f (issec-pred-ℤ-Mod k x))))

compute-map-preserves-succ-map-ℤ-Mod' :
  (k : ℕ) (f : ℤ-Mod k → ℤ-Mod k) → (f ∘ succ-ℤ-Mod k) ~ (succ-ℤ-Mod k ∘ f) →
  (x : ℤ) → Id (add-ℤ-Mod k (mod-ℤ k x) (f (zero-ℤ-Mod k))) (f (mod-ℤ k x))
compute-map-preserves-succ-map-ℤ-Mod' k f H (inl zero-ℕ) =
  ( ap (add-ℤ-Mod' k (f (zero-ℤ-Mod k))) (mod-neg-one-ℤ k)) ∙
  ( ( inv (is-add-neg-one-pred-ℤ-Mod k (f (zero-ℤ-Mod k)))) ∙
    ( ( ap (pred-ℤ-Mod k) (ap f (inv (mod-zero-ℤ k)))) ∙
      ( ( inv
          ( preserves-pred-preserves-succ-map-ℤ-Mod k f H (mod-ℤ k zero-ℤ))) ∙
        ( inv (ap f (preserves-predecessor-mod-ℤ k zero-ℤ))))))
compute-map-preserves-succ-map-ℤ-Mod' k f H (inl (succ-ℕ x)) =
  ( ap
    ( add-ℤ-Mod' k (f (zero-ℤ-Mod k)))
    ( preserves-predecessor-mod-ℤ k (inl x))) ∙
  ( ( left-predecessor-law-add-ℤ-Mod k (mod-ℤ k (inl x)) (f (zero-ℤ-Mod k))) ∙
    ( ( ap
        ( pred-ℤ-Mod k)
        ( compute-map-preserves-succ-map-ℤ-Mod' k f H (inl x))) ∙
      ( ( inv
          ( preserves-pred-preserves-succ-map-ℤ-Mod k f H (mod-ℤ k (inl x)))) ∙
        ( ap f (inv (preserves-predecessor-mod-ℤ k (inl x)))))))
compute-map-preserves-succ-map-ℤ-Mod' k f H (inr (inl star)) =
  ( ap (add-ℤ-Mod' k (f (zero-ℤ-Mod k))) (mod-zero-ℤ k)) ∙
  ( ( left-unit-law-add-ℤ-Mod k (f (zero-ℤ-Mod k))) ∙
    ( ap f (inv (mod-zero-ℤ k))))
compute-map-preserves-succ-map-ℤ-Mod' k f H (inr (inr zero-ℕ)) =
  ( ap-add-ℤ-Mod k (mod-one-ℤ k) (ap f (inv (mod-zero-ℤ k)))) ∙
  ( ( inv (is-add-one-succ-ℤ-Mod k (f (mod-ℤ k zero-ℤ)))) ∙
    ( ( inv (H (mod-ℤ k zero-ℤ))) ∙
      ( ap f (inv (preserves-successor-mod-ℤ k zero-ℤ)))))
compute-map-preserves-succ-map-ℤ-Mod' k f H (inr (inr (succ-ℕ x))) =
  ( ap
    ( add-ℤ-Mod' k (f (zero-ℤ-Mod k)))
    ( preserves-successor-mod-ℤ k (inr (inr x)))) ∙
  ( ( left-successor-law-add-ℤ-Mod k
      ( mod-ℤ k (inr (inr x)))
      ( f (zero-ℤ-Mod k))) ∙
    ( ( ap
        ( succ-ℤ-Mod k)
        ( compute-map-preserves-succ-map-ℤ-Mod' k f H (inr (inr x)))) ∙
      ( ( inv (H (mod-ℤ k (inr (inr x))))) ∙
        ( ap f (inv (preserves-successor-mod-ℤ k (inr (inr x))))))))

compute-map-preserves-succ-map-ℤ-Mod :
  (k : ℕ) (f : ℤ-Mod k → ℤ-Mod k) (H : (f ∘ succ-ℤ-Mod k) ~ (succ-ℤ-Mod k ∘ f))
  (x : ℤ-Mod k) → Id (add-ℤ-Mod k x (f (zero-ℤ-Mod k))) (f x)
compute-map-preserves-succ-map-ℤ-Mod k f H x =
  ( ap (add-ℤ-Mod' k (f (zero-ℤ-Mod k))) (inv (issec-int-ℤ-Mod k x))) ∙
  ( ( compute-map-preserves-succ-map-ℤ-Mod' k f H (int-ℤ-Mod k x)) ∙
    ( ap f (issec-int-ℤ-Mod k x)))

isretr-equiv-Eq-Cyclic-Type :
  (k : ℕ) →
  (equiv-Eq-Cyclic-Type k ∘ Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k)) ~ id
isretr-equiv-Eq-Cyclic-Type k e =
  eq-htpy-equiv-Cyclic-Type k
    ( ℤ-Mod-Cyclic-Type k)
    ( ℤ-Mod-Cyclic-Type k)
    ( equiv-Eq-Cyclic-Type k (Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) e))
    ( e)
    ( compute-map-preserves-succ-map-ℤ-Mod
      ( k)
      ( map-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k) e)
      ( coherence-square-equiv-Cyclic-Type
        ( k)
        ( ℤ-Mod-Cyclic-Type k)
        ( ℤ-Mod-Cyclic-Type k)
        ( e)))

is-equiv-Eq-equiv-Cyclic-Type :
  (k : ℕ) (X : Cyclic-Type lzero k) → is-equiv (Eq-equiv-Cyclic-Type k X)
is-equiv-Eq-equiv-Cyclic-Type k X =
  apply-universal-property-trunc-Prop
    ( mere-eq-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) X)
    ( is-equiv-Prop (Eq-equiv-Cyclic-Type k X))
    ( λ { refl →
          is-equiv-has-inverse
            ( equiv-Eq-Cyclic-Type k)
            ( issec-equiv-Eq-Cyclic-Type k)
            ( isretr-equiv-Eq-Cyclic-Type k)})

equiv-compute-Ω-Cyclic-Type :
  (k : ℕ) → type-Ω (pair (Cyclic-Type lzero k) (ℤ-Mod-Cyclic-Type k)) ≃ ℤ-Mod k
equiv-compute-Ω-Cyclic-Type k =
  ( pair
    ( Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k))
    ( is-equiv-Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k))) ∘e
  ( extensionality-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k))

map-equiv-compute-Ω-Cyclic-Type :
  (k : ℕ) → type-Ω (pair (Cyclic-Type lzero k) (ℤ-Mod-Cyclic-Type k)) → ℤ-Mod k
map-equiv-compute-Ω-Cyclic-Type k = map-equiv (equiv-compute-Ω-Cyclic-Type k)

preserves-concat-equiv-eq-Cyclic-Type :
  (k : ℕ) (X Y Z : Cyclic-Type lzero k) (p : Id X Y) (q : Id Y Z) →
  Id ( equiv-eq-Cyclic-Type k X Z (p ∙ q))
     ( comp-equiv-Cyclic-Type k X Y Z
       ( equiv-eq-Cyclic-Type k Y Z q)
       ( equiv-eq-Cyclic-Type k X Y p))
preserves-concat-equiv-eq-Cyclic-Type k X .X Z refl q =
  inv (right-unit-law-comp-equiv-Cyclic-Type k X Z (equiv-eq-Cyclic-Type k X Z q))

preserves-comp-Eq-equiv-Cyclic-Type :
  (k : ℕ)
  (e f : equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k)) →
  Id ( Eq-equiv-Cyclic-Type k
       ( ℤ-Mod-Cyclic-Type k)
       ( comp-equiv-Cyclic-Type k
         ( ℤ-Mod-Cyclic-Type k)
         ( ℤ-Mod-Cyclic-Type k)
         ( ℤ-Mod-Cyclic-Type k)
         ( f)
         ( e)))
     ( add-ℤ-Mod k
       ( Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) e)
       ( Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) f))
preserves-comp-Eq-equiv-Cyclic-Type k e f =
  inv
  ( compute-map-preserves-succ-map-ℤ-Mod k
    ( map-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k) f)
    ( coherence-square-equiv-Cyclic-Type k
      ( ℤ-Mod-Cyclic-Type k)
      ( ℤ-Mod-Cyclic-Type k)
      ( f))
    ( map-equiv-Cyclic-Type k
      ( ℤ-Mod-Cyclic-Type k)
      ( ℤ-Mod-Cyclic-Type k)
      ( e)
      ( zero-ℤ-Mod k)))

preserves-concat-equiv-compute-Ω-Cyclic-Type :
  (k : ℕ) (p q : type-Ω (Cyclic-Type-Pointed-Type k)) →
  Id ( map-equiv (equiv-compute-Ω-Cyclic-Type k) (p ∙ q))
     ( add-ℤ-Mod k
       ( map-equiv (equiv-compute-Ω-Cyclic-Type k) p)
       ( map-equiv (equiv-compute-Ω-Cyclic-Type k) q))
preserves-concat-equiv-compute-Ω-Cyclic-Type k p q =
  ( ap
    ( Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k))
    ( preserves-concat-equiv-eq-Cyclic-Type k
      ( ℤ-Mod-Cyclic-Type k)
      ( ℤ-Mod-Cyclic-Type k)
      ( ℤ-Mod-Cyclic-Type k)
      ( p)
      ( q))) ∙
  ( preserves-comp-Eq-equiv-Cyclic-Type k
    ( equiv-eq-Cyclic-Type k ( ℤ-Mod-Cyclic-Type k) ( ℤ-Mod-Cyclic-Type k) p)
    ( equiv-eq-Cyclic-Type k ( ℤ-Mod-Cyclic-Type k) ( ℤ-Mod-Cyclic-Type k) q))

type-Ω-Cyclic-Type : (k : ℕ) → UU (lsuc lzero)
type-Ω-Cyclic-Type k = Id (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k)

is-set-type-Ω-Cyclic-Type : (k : ℕ) → is-set (type-Ω-Cyclic-Type k)
is-set-type-Ω-Cyclic-Type k =
  is-set-equiv
    ( ℤ-Mod k)
    ( equiv-compute-Ω-Cyclic-Type k)
    ( is-set-ℤ-Mod k)

Ω-Cyclic-Type-Group : (k : ℕ) → Group (lsuc lzero)
Ω-Cyclic-Type-Group k =
  loop-space-Group
    ( pair (Cyclic-Type lzero k) (ℤ-Mod-Cyclic-Type k))
    ( is-set-type-Ω-Cyclic-Type k)

equiv-Ω-Cyclic-Type-Group : (k : ℕ) → equiv-Group (Ω-Cyclic-Type-Group k) (ℤ-Mod-Group k)
pr1 (equiv-Ω-Cyclic-Type-Group k) = equiv-compute-Ω-Cyclic-Type k
pr2 (equiv-Ω-Cyclic-Type-Group k) =
  preserves-concat-equiv-compute-Ω-Cyclic-Type k

iso-Ω-Cyclic-Type-Group :
  (k : ℕ) → type-iso-Group (Ω-Cyclic-Type-Group k) (ℤ-Mod-Group k)
iso-Ω-Cyclic-Type-Group k =
  iso-equiv-Group
    ( Ω-Cyclic-Type-Group k)
    ( ℤ-Mod-Group k)
    ( equiv-Ω-Cyclic-Type-Group k)
```
