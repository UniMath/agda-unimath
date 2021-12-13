---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module the-circle.cyclic-types where

open import the-circle.infinite-cyclic-types public

Fin-Endo : ℕ → Endo lzero
pr1 (Fin-Endo k) = Fin k
pr2 (Fin-Endo k) = succ-Fin

ℤ-Mod-Endo : (k : ℕ) → Endo lzero
pr1 (ℤ-Mod-Endo k) = ℤ-Mod k
pr2 (ℤ-Mod-Endo k) = succ-ℤ-Mod k

is-cyclic-Endo : {l : Level} → ℕ → Endo l → UU l
is-cyclic-Endo k X = mere-equiv-Endo (ℤ-Mod-Endo k) X

Cyclic : (l : Level) → ℕ → UU (lsuc l)
Cyclic l k = Σ (Endo l) (is-cyclic-Endo k)

ℤ-Mod-Cyclic : (k : ℕ) → Cyclic lzero k
pr1 (ℤ-Mod-Cyclic k) = ℤ-Mod-Endo k
pr2 (ℤ-Mod-Cyclic k) = refl-mere-equiv-Endo (ℤ-Mod-Endo k)

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
is-contr-total-equiv-Cyclic zero-ℕ X = is-contr-total-equiv-Infinite-Cyclic X
is-contr-total-equiv-Cyclic (succ-ℕ k) X =
  is-contr-total-Eq-substructure
    ( is-contr-total-equiv-Endo (endo-Cyclic (succ-ℕ k) X))
    ( λ Y → is-prop-type-trunc-Prop)
    ( endo-Cyclic (succ-ℕ k) X)
    ( id-equiv-Endo (endo-Cyclic (succ-ℕ k) X))
    ( mere-equiv-endo-Cyclic (succ-ℕ k) X)

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
pr1 (equiv-Eq-Cyclic zero-ℕ x) = equiv-add-ℤ' x
pr2 (equiv-Eq-Cyclic zero-ℕ x) y = left-successor-law-add-ℤ y x
pr1 (equiv-Eq-Cyclic (succ-ℕ k) x) = equiv-add-Fin' x
pr2 (equiv-Eq-Cyclic (succ-ℕ k) x) y = left-successor-law-add-Fin y x

issec-equiv-Eq-Cyclic :
  (k : ℕ) → (Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k) ∘ equiv-Eq-Cyclic k) ~ id
issec-equiv-Eq-Cyclic zero-ℕ x = left-unit-law-add-ℤ x
issec-equiv-Eq-Cyclic (succ-ℕ k) x = left-unit-law-add-Fin x

preserves-pred-preserves-succ-map-ℤ :
  (f : ℤ → ℤ) → (f ∘ succ-ℤ) ~ (succ-ℤ ∘ f) → (f ∘ pred-ℤ) ~ (pred-ℤ ∘ f)
preserves-pred-preserves-succ-map-ℤ f H x =
  ( inv (isretr-pred-ℤ (f (pred-ℤ x)))) ∙
  ( ( ap pred-ℤ (inv (H (pred-ℤ x)) ∙ ( ap f (issec-pred-ℤ x)))))

preserves-add-preserves-succ-map-ℤ :
  (f : ℤ → ℤ) → (f ∘ succ-ℤ) ~ (succ-ℤ ∘ f) →
  (x : ℤ) → (f ∘ add-ℤ x) ~ (add-ℤ x ∘ f)
preserves-add-preserves-succ-map-ℤ f H (inl zero-ℕ) =
  preserves-pred-preserves-succ-map-ℤ f H
preserves-add-preserves-succ-map-ℤ f H (inl (succ-ℕ x)) y =
   ( preserves-pred-preserves-succ-map-ℤ f H (add-ℤ (inl x) y)) ∙
   ( ap pred-ℤ (preserves-add-preserves-succ-map-ℤ f H (inl x) y))
preserves-add-preserves-succ-map-ℤ f H (inr (inl star)) = refl-htpy
preserves-add-preserves-succ-map-ℤ f H (inr (inr zero-ℕ)) = H
preserves-add-preserves-succ-map-ℤ f H (inr (inr (succ-ℕ x))) y =
  ( H (add-ℤ (inr (inr x)) y)) ∙
  ( ap succ-ℤ (preserves-add-preserves-succ-map-ℤ f H (inr (inr x)) y))

compute-map-preserves-succ-map-Fin' :
  {k : ℕ} (f : Fin (succ-ℕ k) → Fin (succ-ℕ k)) →
  (f ∘ succ-Fin) ~ (succ-Fin ∘ f) →
  (x : ℕ) → Id (f (mod-succ-ℕ k x)) (add-Fin (mod-succ-ℕ k x) (f zero-Fin))
compute-map-preserves-succ-map-Fin' f H zero-ℕ =
  inv (left-unit-law-add-Fin (f zero-Fin))
compute-map-preserves-succ-map-Fin' {k} f H (succ-ℕ x) =
  ( H (mod-succ-ℕ k x)) ∙
  ( ( ap succ-Fin (compute-map-preserves-succ-map-Fin' f H x)) ∙
    ( inv (left-successor-law-add-Fin (mod-succ-ℕ k x) (f zero-Fin))))

compute-map-preserves-succ-map-Fin :
  {k : ℕ} (f : Fin (succ-ℕ k) → Fin (succ-ℕ k)) →
  (f ∘ succ-Fin) ~ (succ-Fin ∘ f) →
  (x : Fin (succ-ℕ k)) → Id (f x) (add-Fin x (f zero-Fin))
compute-map-preserves-succ-map-Fin f H x =
  ( ap f (inv (issec-nat-Fin x))) ∙
  ( ( compute-map-preserves-succ-map-Fin' f H (nat-Fin x)) ∙
    ( ap (add-Fin' (f zero-Fin)) (issec-nat-Fin x)))

isretr-equiv-Eq-Cyclic :
  (k : ℕ) → (equiv-Eq-Cyclic k ∘ Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k)) ~ id
isretr-equiv-Eq-Cyclic k e =
  eq-htpy-equiv-Cyclic k
    ( ℤ-Mod-Cyclic k)
    ( ℤ-Mod-Cyclic k)
    ( equiv-Eq-Cyclic k (Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k) e))
    ( e)
    ( λ x →
      ( inv
        {! preserves-add-preserves-!}) ∙
      {!!})

-- isretr-equiv-Eq-Cyclic :
--   (k : ℕ) → (equiv-Eq-Cyclic k ∘ Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k)) ~ id
-- isretr-equiv-Eq-Cyclic zero-ℕ e =
--   eq-htpy-equiv-Cyclic zero-ℕ
--     ( ℤ-Infinite-Cyclic)
--     ( ℤ-Infinite-Cyclic)
--     ( equiv-Eq-Cyclic zero-ℕ (Eq-equiv-Cyclic zero-ℕ ℤ-Infinite-Cyclic e))
--     ( e)
--     ( λ x →
--       ( inv
--         ( preserves-add-preserves-succ-map-ℤ
--           ( map-equiv-Cyclic zero-ℕ ℤ-Infinite-Cyclic ℤ-Infinite-Cyclic e)
--           ( coherence-square-equiv-Cyclic zero-ℕ
--               ℤ-Infinite-Cyclic
--               ℤ-Infinite-Cyclic
--               e) x zero-ℤ)) ∙
--       ( ap (map-equiv (pr1 e)) (right-unit-law-add-ℤ x)))
-- isretr-equiv-Eq-Cyclic (succ-ℕ k) e =
--   eq-htpy-equiv-Cyclic
--     ( succ-ℕ k)
--     ( Fin-Cyclic k)
--     ( Fin-Cyclic k)
--     ( equiv-Eq-Cyclic (succ-ℕ k) (Eq-equiv-Cyclic (succ-ℕ k) (Fin-Cyclic k) e))
--     ( e)
--     ( inv-htpy
--         ( compute-map-preserves-succ-map-Fin
--           ( map-equiv-Cyclic (succ-ℕ k) (Fin-Cyclic k) (Fin-Cyclic k) e)
--           ( coherence-square-equiv-Cyclic
--             ( succ-ℕ k)
--             ( Fin-Cyclic k)
--             ( Fin-Cyclic k)
--             ( e))))

-- is-equiv-Eq-equiv-Cyclic :
--   (k : ℕ) (X : Cyclic lzero k) → is-equiv (Eq-equiv-Cyclic k X)
-- is-equiv-Eq-equiv-Cyclic k X =
--   apply-universal-property-trunc-Prop
--     ( mere-eq-Cyclic k (ℤ-Mod-Cyclic k) X)
--     ( is-equiv-Prop (Eq-equiv-Cyclic k X))
--     ( λ { refl →
--           is-equiv-has-inverse
--             ( equiv-Eq-Cyclic k)
--             ( issec-equiv-Eq-Cyclic k)
--             ( isretr-equiv-Eq-Cyclic k)})

-- equiv-compute-Ω-Cyclic :
--   (k : ℕ) →
--   type-Ω (pair (Cyclic lzero k) (ℤ-Mod-Cyclic k)) ≃ ℤ-Mod k
-- equiv-compute-Ω-Cyclic k =
--   ( pair
--     ( Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k))
--     ( is-equiv-Eq-equiv-Cyclic k (ℤ-Mod-Cyclic k))) ∘e
--   ( extensionality-Cyclic k (ℤ-Mod-Cyclic k) (ℤ-Mod-Cyclic k))

-- ```
