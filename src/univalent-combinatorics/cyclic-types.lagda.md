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
open import foundation.coproduct-types using (coprod; inl; inr)
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
  ( is-set; is-set-Prop; is-set-equiv'; is-set-equiv)
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

```agda
is-cyclic-Endo : {l : Level} → ℕ → Endo l → UU l
is-cyclic-Endo k X = mere-equiv-Endo (ℤ-Mod-Endo k) X

Cyclic : (l : Level) → ℕ → UU (lsuc l)
Cyclic l k = Σ (Endo l) (is-cyclic-Endo k)

ℤ-Mod-Cyclic : (k : ℕ) → Cyclic lzero k
pr1 (ℤ-Mod-Cyclic k) = ℤ-Mod-Endo k
pr2 (ℤ-Mod-Cyclic k) = refl-mere-equiv-Endo (ℤ-Mod-Endo k)

Cyclic-Pointed-Type : (k : ℕ) → Pointed-Type (lsuc lzero)
pr1 (Cyclic-Pointed-Type k) = Cyclic lzero k
pr2 (Cyclic-Pointed-Type k) = ℤ-Mod-Cyclic k

endo-Cyclic : {l : Level} (k : ℕ) → Cyclic l k → Endo l
endo-Cyclic k = pr1

type-Cyclic : {l : Level} (k : ℕ) → Cyclic l k → UU l
type-Cyclic k X = type-Endo (endo-Cyclic k X)

Fin-Cyclic : (k : ℕ) → Cyclic lzero (succ-ℕ k)
pr1 (Fin-Cyclic k) = Fin-Endo (succ-ℕ k)
pr2 (Fin-Cyclic k) = refl-mere-equiv-Endo (Fin-Endo (succ-ℕ k))

endo-ℤ-Mod-Cyclic : (k : ℕ) → Endo lzero
endo-ℤ-Mod-Cyclic k = endo-Cyclic k (ℤ-Mod-Cyclic k)

mere-equiv-endo-Cyclic :
  {l : Level} (k : ℕ) (X : Cyclic l k) →
  mere-equiv-Endo (endo-ℤ-Mod-Cyclic k) (endo-Cyclic k X)
mere-equiv-endo-Cyclic zero-ℕ X = pr2 X
mere-equiv-endo-Cyclic (succ-ℕ k) X = pr2 X

endomorphism-Cyclic :
  {l : Level} (k : ℕ) (X : Cyclic l k) → type-Cyclic k X → type-Cyclic k X
endomorphism-Cyclic k X = endomorphism-Endo (endo-Cyclic k X)

module _
  {l1 l2 : Level} (k : ℕ) (X : Cyclic l1 k) (Y : Cyclic l2 k)
  where
  
  equiv-Cyclic : UU (l1 ⊔ l2)
  equiv-Cyclic = equiv-Endo (endo-Cyclic k X) (endo-Cyclic k Y)

  equiv-equiv-Cyclic : equiv-Cyclic → type-Cyclic k X ≃ type-Cyclic k Y
  equiv-equiv-Cyclic = equiv-equiv-Endo (endo-Cyclic k X) (endo-Cyclic k Y)

  map-equiv-Cyclic : equiv-Cyclic → type-Cyclic k X → type-Cyclic k Y
  map-equiv-Cyclic e = map-equiv-Endo (endo-Cyclic k X) (endo-Cyclic k Y) e

  coherence-square-equiv-Cyclic :
    (e : equiv-Cyclic) →
    coherence-square
      ( map-equiv-Cyclic e)
      ( endomorphism-Cyclic k X)
      ( endomorphism-Cyclic k Y)
      ( map-equiv-Cyclic e)
  coherence-square-equiv-Cyclic e = pr2 e

module _
  {l : Level} (k : ℕ) (X : Cyclic l k)
  where
  
  is-set-type-Cyclic : is-set (type-Cyclic k X)
  is-set-type-Cyclic =
    apply-universal-property-trunc-Prop
      ( mere-equiv-endo-Cyclic k X)
      ( is-set-Prop (type-Cyclic k X))
      ( λ e →
        is-set-equiv'
          ( ℤ-Mod k)
          ( equiv-equiv-Cyclic k (ℤ-Mod-Cyclic k) X e)
          ( is-set-ℤ-Mod k))

  id-equiv-Cyclic : equiv-Cyclic k X X
  id-equiv-Cyclic = id-equiv-Endo (endo-Cyclic k X)
                                                 
  equiv-eq-Cyclic : (Y : Cyclic l k) → Id X Y → equiv-Cyclic k X Y
  equiv-eq-Cyclic .X refl = id-equiv-Cyclic

is-contr-total-equiv-Cyclic :
  {l1 : Level} (k : ℕ) (X : Cyclic l1 k) →
  is-contr (Σ (Cyclic l1 k) (equiv-Cyclic k X))
is-contr-total-equiv-Cyclic k X =
  is-contr-total-Eq-subtype
    ( is-contr-total-equiv-Endo (endo-Cyclic k X))
    ( λ Y → is-prop-type-trunc-Prop)
    ( endo-Cyclic k X)
    ( id-equiv-Endo (endo-Cyclic k X))
    ( mere-equiv-endo-Cyclic k X)

module _
  {l : Level} (k : ℕ) (X : Cyclic l k)
  where
  
  is-equiv-equiv-eq-Cyclic : (Y : Cyclic l k) → is-equiv (equiv-eq-Cyclic k X Y)
  is-equiv-equiv-eq-Cyclic =
    fundamental-theorem-id X
      ( id-equiv-Cyclic k X)
      ( is-contr-total-equiv-Cyclic k X)
      ( equiv-eq-Cyclic k X)

  extensionality-Cyclic : (Y : Cyclic l k) → Id X Y ≃ equiv-Cyclic k X Y
  pr1 (extensionality-Cyclic Y) = equiv-eq-Cyclic k X Y
  pr2 (extensionality-Cyclic Y) = is-equiv-equiv-eq-Cyclic Y
  
  eq-equiv-Cyclic : (Y : Cyclic l k) → equiv-Cyclic k X Y → Id X Y
  eq-equiv-Cyclic Y = map-inv-is-equiv (is-equiv-equiv-eq-Cyclic Y)

module _
  {l1 l2 : Level} (k : ℕ) (X : Cyclic l1 k) (Y : Cyclic l2 k)
  where

  htpy-equiv-Cyclic : (e f : equiv-Cyclic k X Y) → UU (l1 ⊔ l2)
  htpy-equiv-Cyclic e f = map-equiv-Cyclic k X Y e ~ map-equiv-Cyclic k X Y f

  refl-htpy-equiv-Cyclic :
    (e : equiv-Cyclic k X Y) → htpy-equiv-Cyclic e e
  refl-htpy-equiv-Cyclic e = refl-htpy

  htpy-eq-equiv-Cyclic :
    (e f : equiv-Cyclic k X Y) → Id e f → htpy-equiv-Cyclic e f
  htpy-eq-equiv-Cyclic e .e refl = refl-htpy-equiv-Cyclic e

  is-contr-total-htpy-equiv-Cyclic :
    (e : equiv-Cyclic k X Y) →
    is-contr (Σ (equiv-Cyclic k X Y) (htpy-equiv-Cyclic e))
  is-contr-total-htpy-equiv-Cyclic e =
    is-contr-equiv'
      ( Σ ( equiv-Endo (endo-Cyclic k X) (endo-Cyclic k Y))
          ( htpy-equiv-Endo (endo-Cyclic k X) (endo-Cyclic k Y) e))
      ( equiv-tot
        ( λ f →
          right-unit-law-Σ-is-contr
            ( λ H →
              is-contr-Π
                ( λ x →
                  is-set-type-Cyclic k Y
                  ( map-equiv-Cyclic k X Y e (endomorphism-Cyclic k X x))
                  ( endomorphism-Cyclic k Y (map-equiv-Cyclic k X Y f x))
                  ( ( H (endomorphism-Cyclic k X x)) ∙
                    ( coherence-square-equiv-Cyclic k X Y f x))
                  ( ( coherence-square-equiv-Cyclic k X Y e x) ∙
                    ( ap (endomorphism-Cyclic k Y) (H x)))))))
      ( is-contr-total-htpy-equiv-Endo (endo-Cyclic k X) (endo-Cyclic k Y) e)

  is-equiv-htpy-eq-equiv-Cyclic :
    (e f : equiv-Cyclic k X Y) → is-equiv (htpy-eq-equiv-Cyclic e f)
  is-equiv-htpy-eq-equiv-Cyclic e =
    fundamental-theorem-id e
      ( refl-htpy-equiv-Cyclic e)
      ( is-contr-total-htpy-equiv-Cyclic e)
      ( htpy-eq-equiv-Cyclic e)

  extensionality-equiv-Cyclic :
    (e f : equiv-Cyclic k X Y) → Id e f ≃ htpy-equiv-Cyclic e f
  pr1 (extensionality-equiv-Cyclic e f) = htpy-eq-equiv-Cyclic e f
  pr2 (extensionality-equiv-Cyclic e f) = is-equiv-htpy-eq-equiv-Cyclic e f

  eq-htpy-equiv-Cyclic :
    (e f : equiv-Cyclic k X Y) → htpy-equiv-Cyclic e f → Id e f
  eq-htpy-equiv-Cyclic e f = map-inv-equiv (extensionality-equiv-Cyclic e f)

comp-equiv-Cyclic :
  {l1 l2 l3 : Level} (k : ℕ) (X : Cyclic l1 k) (Y : Cyclic l2 k)
  (Z : Cyclic l3 k) →
  equiv-Cyclic k Y Z → equiv-Cyclic k X Y → equiv-Cyclic k X Z
comp-equiv-Cyclic k X Y Z =
  comp-equiv-Endo
    ( endo-Cyclic k X)
    ( endo-Cyclic k Y)
    ( endo-Cyclic k Z)

inv-equiv-Cyclic :
  {l1 l2 : Level} (k : ℕ) (X : Cyclic l1 k) (Y : Cyclic l2 k) →
  equiv-Cyclic k X Y → equiv-Cyclic k Y X
inv-equiv-Cyclic k X Y = inv-equiv-Endo (endo-Cyclic k X) (endo-Cyclic k Y)

associative-comp-equiv-Cyclic :
  {l1 l2 l3 l4 : Level} (k : ℕ) (X : Cyclic l1 k) (Y : Cyclic l2 k)
  (Z : Cyclic l3 k) (W : Cyclic l4 k) (g : equiv-Cyclic k Z W)
  (f : equiv-Cyclic k Y Z) (e : equiv-Cyclic k X Y) →
  Id ( comp-equiv-Cyclic k X Y W (comp-equiv-Cyclic k Y Z W g f) e)
     ( comp-equiv-Cyclic k X Z W g (comp-equiv-Cyclic k X Y Z f e))
associative-comp-equiv-Cyclic k X Y Z W g f e =
  eq-htpy-equiv-Cyclic k X W
    ( comp-equiv-Cyclic k X Y W (comp-equiv-Cyclic k Y Z W g f) e)
    ( comp-equiv-Cyclic k X Z W g (comp-equiv-Cyclic k X Y Z f e))
    ( refl-htpy)

module _
  {l1 l2 : Level} (k : ℕ) (X : Cyclic l1 k) (Y : Cyclic l2 k)
  (e : equiv-Cyclic k X Y)
  where
  
  left-unit-law-comp-equiv-Cyclic :
    Id (comp-equiv-Cyclic k X Y Y (id-equiv-Cyclic k Y) e) e
  left-unit-law-comp-equiv-Cyclic =
    eq-htpy-equiv-Cyclic k X Y
      ( comp-equiv-Cyclic k X Y Y (id-equiv-Cyclic k Y) e)
      ( e)
      ( refl-htpy)

  right-unit-law-comp-equiv-Cyclic :
    Id (comp-equiv-Cyclic k X X Y e (id-equiv-Cyclic k X)) e
  right-unit-law-comp-equiv-Cyclic =
    eq-htpy-equiv-Cyclic k X Y
      ( comp-equiv-Cyclic k X X Y e (id-equiv-Cyclic k X))
      ( e)
      ( refl-htpy)

  left-inverse-law-comp-equiv-Cyclic :
    Id ( comp-equiv-Cyclic k X Y X (inv-equiv-Cyclic k X Y e) e)
       ( id-equiv-Cyclic k X)
  left-inverse-law-comp-equiv-Cyclic =
    eq-htpy-equiv-Cyclic k X X
      ( comp-equiv-Cyclic k X Y X (inv-equiv-Cyclic k X Y e) e)
      ( id-equiv-Cyclic k X)
      ( isretr-map-inv-equiv (equiv-equiv-Cyclic k X Y e))

  right-inverse-law-comp-equiv-Cyclic :
    Id ( comp-equiv-Cyclic k Y X Y e (inv-equiv-Cyclic k X Y e))
       ( id-equiv-Cyclic k Y)
  right-inverse-law-comp-equiv-Cyclic =
    eq-htpy-equiv-Cyclic k Y Y
      ( comp-equiv-Cyclic k Y X Y e (inv-equiv-Cyclic k X Y e))
      ( id-equiv-Cyclic k Y)
      ( issec-map-inv-equiv (equiv-equiv-Cyclic k X Y e))

mere-eq-Cyclic : {l : Level} (k : ℕ) (X Y : Cyclic l k) → mere-eq X Y
mere-eq-Cyclic k X Y =
  apply-universal-property-trunc-Prop
    ( mere-equiv-endo-Cyclic k X)
    ( mere-eq-Prop X Y)
    ( λ e →
      apply-universal-property-trunc-Prop
        ( mere-equiv-endo-Cyclic k Y)
        ( mere-eq-Prop X Y)
        ( λ f →
          unit-trunc-Prop
            ( eq-equiv-Cyclic k X Y
              ( comp-equiv-Cyclic k X (ℤ-Mod-Cyclic k) Y f
                ( inv-equiv-Cyclic k (ℤ-Mod-Cyclic k) X e)))))

is-path-connected-Cyclic : (k : ℕ) → is-path-connected (Cyclic lzero k)
is-path-connected-Cyclic k =
  is-path-connected-mere-eq
    ( ℤ-Mod-Cyclic k)
    ( mere-eq-Cyclic k (ℤ-Mod-Cyclic k))

Eq-Cyclic : (k : ℕ) → Cyclic lzero k → UU lzero
Eq-Cyclic k X = type-Cyclic k X

refl-Eq-Cyclic : (k : ℕ) → Eq-Cyclic k (ℤ-Mod-Cyclic k)
refl-Eq-Cyclic k = zero-ℤ-Mod k

Eq-equiv-Cyclic :
  (k : ℕ) (X : Cyclic lzero k) →
  equiv-Cyclic k (ℤ-Mod-Cyclic k) X → Eq-Cyclic k X
Eq-equiv-Cyclic k X e =
  map-equiv-Cyclic k (ℤ-Mod-Cyclic k) X e (zero-ℤ-Mod k)

equiv-Eq-Cyclic :
  (k : ℕ) → Eq-Cyclic k (ℤ-Mod-Cyclic k) →
  equiv-Cyclic k (ℤ-Mod-Cyclic k) (ℤ-Mod-Cyclic k)
pr1 (equiv-Eq-Cyclic k x) = equiv-add-ℤ-Mod' k x
pr2 (equiv-Eq-Cyclic k x) y = left-successor-law-add-ℤ-Mod k y x

issec-equiv-Eq-Cyclic :
  (k : ℕ) → (Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k) ∘ equiv-Eq-Cyclic k) ~ id
issec-equiv-Eq-Cyclic zero-ℕ x = left-unit-law-add-ℤ x
issec-equiv-Eq-Cyclic (succ-ℕ k) x = left-unit-law-add-Fin x

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

isretr-equiv-Eq-Cyclic :
  (k : ℕ) → (equiv-Eq-Cyclic k ∘ Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k)) ~ id
isretr-equiv-Eq-Cyclic k e =
  eq-htpy-equiv-Cyclic k
    ( ℤ-Mod-Cyclic k)
    ( ℤ-Mod-Cyclic k)
    ( equiv-Eq-Cyclic k (Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k) e))
    ( e)
    ( compute-map-preserves-succ-map-ℤ-Mod
      ( k)
      ( map-equiv-Cyclic k (ℤ-Mod-Cyclic k) (ℤ-Mod-Cyclic k) e)
      ( coherence-square-equiv-Cyclic
        ( k)
        ( ℤ-Mod-Cyclic k)
        ( ℤ-Mod-Cyclic k)
        ( e)))

is-equiv-Eq-equiv-Cyclic :
  (k : ℕ) (X : Cyclic lzero k) → is-equiv (Eq-equiv-Cyclic k X)
is-equiv-Eq-equiv-Cyclic k X =
  apply-universal-property-trunc-Prop
    ( mere-eq-Cyclic k (ℤ-Mod-Cyclic k) X)
    ( is-equiv-Prop (Eq-equiv-Cyclic k X))
    ( λ { refl →
          is-equiv-has-inverse
            ( equiv-Eq-Cyclic k)
            ( issec-equiv-Eq-Cyclic k)
            ( isretr-equiv-Eq-Cyclic k)})

equiv-compute-Ω-Cyclic :
  (k : ℕ) → type-Ω (pair (Cyclic lzero k) (ℤ-Mod-Cyclic k)) ≃ ℤ-Mod k
equiv-compute-Ω-Cyclic k =
  ( pair
    ( Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k))
    ( is-equiv-Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k))) ∘e
  ( extensionality-Cyclic k (ℤ-Mod-Cyclic k) (ℤ-Mod-Cyclic k))

map-equiv-compute-Ω-Cyclic :
  (k : ℕ) → type-Ω (pair (Cyclic lzero k) (ℤ-Mod-Cyclic k)) → ℤ-Mod k
map-equiv-compute-Ω-Cyclic k = map-equiv (equiv-compute-Ω-Cyclic k)

preserves-concat-equiv-eq-Cyclic :
  (k : ℕ) (X Y Z : Cyclic lzero k) (p : Id X Y) (q : Id Y Z) →
  Id ( equiv-eq-Cyclic k X Z (p ∙ q))
     ( comp-equiv-Cyclic k X Y Z
       ( equiv-eq-Cyclic k Y Z q)
       ( equiv-eq-Cyclic k X Y p))
preserves-concat-equiv-eq-Cyclic k X .X Z refl q =
  inv (right-unit-law-comp-equiv-Cyclic k X Z (equiv-eq-Cyclic k X Z q))

preserves-comp-Eq-equiv-Cyclic :
  (k : ℕ) (e f : equiv-Cyclic k (ℤ-Mod-Cyclic k) (ℤ-Mod-Cyclic k)) →
  Id ( Eq-equiv-Cyclic k
       ( ℤ-Mod-Cyclic k)
       ( comp-equiv-Cyclic k
         ( ℤ-Mod-Cyclic k)
         ( ℤ-Mod-Cyclic k)
         ( ℤ-Mod-Cyclic k)
         ( f)
         ( e)))
     ( add-ℤ-Mod k
       ( Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k) e)
       ( Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k) f))
preserves-comp-Eq-equiv-Cyclic k e f =
  inv
  ( compute-map-preserves-succ-map-ℤ-Mod k
    ( map-equiv-Cyclic k (ℤ-Mod-Cyclic k) (ℤ-Mod-Cyclic k) f)
    ( coherence-square-equiv-Cyclic k
      ( ℤ-Mod-Cyclic k)
      ( ℤ-Mod-Cyclic k)
      ( f))
    ( map-equiv-Cyclic k
      ( ℤ-Mod-Cyclic k)
      ( ℤ-Mod-Cyclic k)
      ( e)
      ( zero-ℤ-Mod k)))

preserves-concat-equiv-compute-Ω-Cyclic :
  (k : ℕ) (p q : type-Ω (Cyclic-Pointed-Type k)) →
  Id ( map-equiv (equiv-compute-Ω-Cyclic k) (p ∙ q))
     ( add-ℤ-Mod k
       ( map-equiv (equiv-compute-Ω-Cyclic k) p)
       ( map-equiv (equiv-compute-Ω-Cyclic k) q))
preserves-concat-equiv-compute-Ω-Cyclic k p q =
  ( ap
    ( Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k))
    ( preserves-concat-equiv-eq-Cyclic k
      ( ℤ-Mod-Cyclic k)
      ( ℤ-Mod-Cyclic k)
      ( ℤ-Mod-Cyclic k)
      ( p)
      ( q))) ∙
  ( preserves-comp-Eq-equiv-Cyclic k
    ( equiv-eq-Cyclic k ( ℤ-Mod-Cyclic k) ( ℤ-Mod-Cyclic k) p)
    ( equiv-eq-Cyclic k ( ℤ-Mod-Cyclic k) ( ℤ-Mod-Cyclic k) q))

type-Ω-Cyclic : (k : ℕ) → UU (lsuc lzero)
type-Ω-Cyclic k = Id (ℤ-Mod-Cyclic k) (ℤ-Mod-Cyclic k)

is-set-type-Ω-Cyclic : (k : ℕ) → is-set (type-Ω-Cyclic k)
is-set-type-Ω-Cyclic k =
  is-set-equiv
    ( ℤ-Mod k)
    ( equiv-compute-Ω-Cyclic k)
    ( is-set-ℤ-Mod k)

Ω-Cyclic-Group : (k : ℕ) → Group (lsuc lzero)
Ω-Cyclic-Group k =
  loop-space-Group
    ( pair (Cyclic lzero k) (ℤ-Mod-Cyclic k))
    ( is-set-type-Ω-Cyclic k)

equiv-Ω-Cyclic-Group : (k : ℕ) → equiv-Group (Ω-Cyclic-Group k) (ℤ-Mod-Group k)
pr1 (equiv-Ω-Cyclic-Group k) = equiv-compute-Ω-Cyclic k
pr2 (equiv-Ω-Cyclic-Group k) = preserves-concat-equiv-compute-Ω-Cyclic k

iso-Ω-Cyclic-Group : (k : ℕ) → type-iso-Group (Ω-Cyclic-Group k) (ℤ-Mod-Group k)
iso-Ω-Cyclic-Group k =
  iso-equiv-Group
    ( Ω-Cyclic-Group k)
    ( ℤ-Mod-Group k)
    ( equiv-Ω-Cyclic-Group k)

```
