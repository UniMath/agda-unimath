---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module synthetic-homotopy-theory.cyclic-types where

open import foundation public
open import groups public
open import univalent-combinatorics public

Endo : (l : Level) → UU (lsuc l)
Endo l = Σ (UU l) (λ X → X → X)

module _
  {l : Level} (X : Endo l)
  where

  type-Endo : UU l
  type-Endo = pr1 X

  endomorphism-Endo : type-Endo → type-Endo
  endomorphism-Endo = pr2 X

ℤ-Endo : Endo lzero
pr1 ℤ-Endo = ℤ
pr2 ℤ-Endo = succ-ℤ

module _
  {l1 l2 : Level} (X : Endo l1) (Y : Endo l2)
  where

  equiv-Endo : UU (l1 ⊔ l2)
  equiv-Endo =
    Σ ( type-Endo X ≃ type-Endo Y)
      ( λ e →
        coherence-square
          ( map-equiv e)
          ( endomorphism-Endo X)
          ( endomorphism-Endo Y)
          ( map-equiv e))

  equiv-equiv-Endo : equiv-Endo → type-Endo X ≃ type-Endo Y
  equiv-equiv-Endo e = pr1 e
  
  map-equiv-Endo : equiv-Endo → type-Endo X → type-Endo Y
  map-equiv-Endo e = map-equiv (equiv-equiv-Endo e)

  coherence-square-equiv-Endo :
    (e : equiv-Endo) →
    coherence-square
      ( map-equiv-Endo e)
      ( endomorphism-Endo X)
      ( endomorphism-Endo Y)
      ( map-equiv-Endo e)
  coherence-square-equiv-Endo e = pr2 e

  mere-equiv-Endo : UU (l1 ⊔ l2)
  mere-equiv-Endo = type-trunc-Prop equiv-Endo

module _
  {l1 : Level} (X : Endo l1)
  where

  id-equiv-Endo : equiv-Endo X X
  pr1 id-equiv-Endo = id-equiv
  pr2 id-equiv-Endo = refl-htpy
  
  refl-mere-equiv-Endo : mere-equiv-Endo X X
  refl-mere-equiv-Endo = unit-trunc-Prop id-equiv-Endo

  equiv-eq-Endo : (Y : Endo l1) → Id X Y → equiv-Endo X Y
  equiv-eq-Endo .X refl = id-equiv-Endo
  
  is-contr-total-equiv-Endo : is-contr (Σ (Endo l1) (equiv-Endo X))
  is-contr-total-equiv-Endo =
    is-contr-total-Eq-structure
      ( λ Y f e → (map-equiv e ∘ endomorphism-Endo X) ~ (f ∘ map-equiv e))
      ( is-contr-total-equiv (type-Endo X))
      ( pair (type-Endo X) id-equiv)
      ( is-contr-total-htpy (endomorphism-Endo X))

  is-equiv-equiv-eq-Endo : (Y : Endo l1) → is-equiv (equiv-eq-Endo Y)
  is-equiv-equiv-eq-Endo =
    fundamental-theorem-id X
      id-equiv-Endo
      is-contr-total-equiv-Endo
      equiv-eq-Endo

  eq-equiv-Endo : (Y : Endo l1) → equiv-Endo X Y → Id X Y
  eq-equiv-Endo Y = map-inv-is-equiv (is-equiv-equiv-eq-Endo Y)

comp-equiv-Endo :
  {l1 l2 l3 : Level} (X : Endo l1) (Y : Endo l2) (Z : Endo l3) →
  equiv-Endo Y Z → equiv-Endo X Y → equiv-Endo X Z
pr1 (comp-equiv-Endo X Y Z f e) = pr1 f ∘e pr1 e
pr2 (comp-equiv-Endo X Y Z f e) =
  coherence-square-comp-horizontal
    ( map-equiv-Endo X Y e)
    ( map-equiv-Endo Y Z f)
    ( endomorphism-Endo X)
    ( endomorphism-Endo Y)
    ( endomorphism-Endo Z)
    ( map-equiv-Endo X Y e)
    ( map-equiv-Endo Y Z f)
    ( coherence-square-equiv-Endo X Y e)
    ( coherence-square-equiv-Endo Y Z f)

inv-equiv-Endo :
  {l1 l2 : Level} (X : Endo l1) (Y : Endo l2) → equiv-Endo X Y → equiv-Endo Y X
pr1 (inv-equiv-Endo X Y e) = inv-equiv (equiv-equiv-Endo X Y e)
pr2 (inv-equiv-Endo X Y e) =
  coherence-square-inv-horizontal
    ( equiv-equiv-Endo X Y e)
    ( endomorphism-Endo X)
    ( endomorphism-Endo Y)
    ( equiv-equiv-Endo X Y e)
    ( coherence-square-equiv-Endo X Y e)

module _
  {l1 l2 : Level} (X : Endo l1) (Y : Endo l2)
  where

  hom-Endo : UU (l1 ⊔ l2)
  hom-Endo =
    Σ ( type-Endo X → type-Endo Y)
      ( λ f → coherence-square f (endomorphism-Endo X) (endomorphism-Endo Y) f)

  map-hom-Endo : hom-Endo → type-Endo X → type-Endo Y
  map-hom-Endo = pr1

  coherence-square-hom-Endo :
    (f : hom-Endo) →
    coherence-square
      ( map-hom-Endo f)
      ( endomorphism-Endo X)
      ( endomorphism-Endo Y)
      ( map-hom-Endo f)
  coherence-square-hom-Endo = pr2

  htpy-hom-Endo : (f g : hom-Endo) → UU (l1 ⊔ l2)
  htpy-hom-Endo f g =
    Σ ( map-hom-Endo f ~ map-hom-Endo g)
      ( λ H →
        ( (H ·r endomorphism-Endo X) ∙h coherence-square-hom-Endo g) ~
        ( coherence-square-hom-Endo f ∙h (endomorphism-Endo Y ·l H)))

  refl-htpy-hom-Endo : (f : hom-Endo) → htpy-hom-Endo f f
  pr1 (refl-htpy-hom-Endo f) = refl-htpy
  pr2 (refl-htpy-hom-Endo f) = inv-htpy right-unit-htpy

  htpy-eq-hom-Endo : (f g : hom-Endo) → Id f g → htpy-hom-Endo f g
  htpy-eq-hom-Endo f .f refl = refl-htpy-hom-Endo f

  is-contr-total-htpy-hom-Endo :
    (f : hom-Endo) → is-contr (Σ hom-Endo (htpy-hom-Endo f))
  is-contr-total-htpy-hom-Endo f =
    is-contr-total-Eq-structure
      ( λ g G H →
        ( (H ·r endomorphism-Endo X) ∙h G) ~
        ( coherence-square-hom-Endo f ∙h (endomorphism-Endo Y ·l H)))
      ( is-contr-total-htpy (map-hom-Endo f))
      ( pair (map-hom-Endo f) refl-htpy)
      ( is-contr-equiv
        ( Σ ( coherence-square
              ( map-hom-Endo f)
              ( endomorphism-Endo X)
              ( endomorphism-Endo Y)
              ( map-hom-Endo f))
            ( λ H → H ~ coherence-square-hom-Endo f))
        ( equiv-tot (λ H → equiv-concat-htpy' H right-unit-htpy))
        ( is-contr-total-htpy' (coherence-square-hom-Endo f)))

  is-equiv-htpy-eq-hom-Endo : (f g : hom-Endo) → is-equiv (htpy-eq-hom-Endo f g)
  is-equiv-htpy-eq-hom-Endo f =
    fundamental-theorem-id f
      ( refl-htpy-hom-Endo f)
      ( is-contr-total-htpy-hom-Endo f)
      ( htpy-eq-hom-Endo f)

  extensionality-hom-Endo : (f g : hom-Endo) → Id f g ≃ htpy-hom-Endo f g
  pr1 (extensionality-hom-Endo f g) = htpy-eq-hom-Endo f g
  pr2 (extensionality-hom-Endo f g) = is-equiv-htpy-eq-hom-Endo f g

  eq-htpy-hom-Endo : (f g : hom-Endo) → htpy-hom-Endo f g → Id f g
  eq-htpy-hom-Endo f g = map-inv-equiv (extensionality-hom-Endo f g)

  hom-equiv-Endo : equiv-Endo X Y → hom-Endo
  pr1 (hom-equiv-Endo e) = map-equiv-Endo X Y e
  pr2 (hom-equiv-Endo e) = coherence-square-equiv-Endo X Y e

  htpy-equiv-Endo : (e f : equiv-Endo X Y) → UU (l1 ⊔ l2)
  htpy-equiv-Endo e f = htpy-hom-Endo (hom-equiv-Endo e) (hom-equiv-Endo f)

  refl-htpy-equiv-Endo : (e : equiv-Endo X Y) → htpy-equiv-Endo e e
  refl-htpy-equiv-Endo e = refl-htpy-hom-Endo (hom-equiv-Endo e)

  htpy-eq-equiv-Endo : (e f : equiv-Endo X Y) → Id e f → htpy-equiv-Endo e f
  htpy-eq-equiv-Endo e .e refl = refl-htpy-equiv-Endo e

  is-contr-total-htpy-equiv-Endo :
    (e : equiv-Endo X Y) → is-contr (Σ (equiv-Endo X Y) (htpy-equiv-Endo e))
  is-contr-total-htpy-equiv-Endo e =
    is-contr-equiv
      ( Σ ( Σ hom-Endo (λ f → is-equiv (map-hom-Endo f)))
          ( λ f → htpy-hom-Endo (hom-equiv-Endo e) (pr1 f)))
      ( equiv-Σ
        ( λ f → htpy-hom-Endo (hom-equiv-Endo e) (pr1 f))
        ( equiv-right-swap-Σ)
        ( λ f → id-equiv))
      ( is-contr-total-Eq-subtype
        ( is-contr-total-htpy-hom-Endo (hom-equiv-Endo e))
        ( λ f → is-subtype-is-equiv (pr1 f))
        ( hom-equiv-Endo e)
        ( refl-htpy-hom-Endo (hom-equiv-Endo e))
        ( pr2 (pr1 e)))

  is-equiv-htpy-eq-equiv-Endo :
    (e f : equiv-Endo X Y) → is-equiv (htpy-eq-equiv-Endo e f)
  is-equiv-htpy-eq-equiv-Endo e =
    fundamental-theorem-id e
      ( refl-htpy-equiv-Endo e)
      ( is-contr-total-htpy-equiv-Endo e)
      ( htpy-eq-equiv-Endo e)

  extensionality-equiv-Endo :
    (e f : equiv-Endo X Y) → Id e f ≃ htpy-equiv-Endo e f
  pr1 (extensionality-equiv-Endo e f) = htpy-eq-equiv-Endo e f
  pr2 (extensionality-equiv-Endo e f) = is-equiv-htpy-eq-equiv-Endo e f

  eq-htpy-equiv-Endo : (e f : equiv-Endo X Y) → htpy-equiv-Endo e f → Id e f
  eq-htpy-equiv-Endo e f =
    map-inv-equiv (extensionality-equiv-Endo e f)

  left-unit-law-comp-equiv-Endo :
    (e : equiv-Endo X Y) → Id (comp-equiv-Endo X Y Y (id-equiv-Endo Y) e) e
  left-unit-law-comp-equiv-Endo e =
    eq-htpy-equiv-Endo
      ( comp-equiv-Endo X Y Y (id-equiv-Endo Y) e)
      ( e)
      ( pair
        ( refl-htpy)
        ( λ x →
          inv
            ( ( right-unit) ∙
              ( right-unit ∙ ap-id (coherence-square-equiv-Endo X Y e x)))))

  right-unit-law-comp-equiv-Endo :
    (e : equiv-Endo X Y) → Id (comp-equiv-Endo X X Y e (id-equiv-Endo X)) e
  right-unit-law-comp-equiv-Endo e =
    eq-htpy-equiv-Endo
      ( comp-equiv-Endo X X Y e (id-equiv-Endo X))
      ( e)
      ( pair
        ( refl-htpy)
        ( λ x → inv right-unit))

module _
  {l : Level} (X : Endo l) (Y : Endo l) (Z : Endo l)
  where

  preserves-concat-equiv-eq-Endo :
    (p : Id X Y) (q : Id Y Z) →
    Id ( equiv-eq-Endo X Z (p ∙ q))
       ( comp-equiv-Endo X Y Z (equiv-eq-Endo Y Z q) (equiv-eq-Endo X Y p))
  preserves-concat-equiv-eq-Endo refl q =
    inv (right-unit-law-comp-equiv-Endo X Z (equiv-eq-Endo X Z q))

module _
  {l1 : Level} (X : Endo l1)
  where
  
  Component-Endo : UU (lsuc l1)
  Component-Endo = Σ (Endo l1) (mere-equiv-Endo X)

  endo-Component-Endo : Component-Endo → Endo l1
  endo-Component-Endo = pr1

  type-Component-Endo : Component-Endo → UU l1
  type-Component-Endo = pr1 ∘ endo-Component-Endo

  endomorphism-Component-Endo :
    (T : Component-Endo) → type-Component-Endo T → type-Component-Endo T
  endomorphism-Component-Endo T = pr2 (endo-Component-Endo T)

  mere-equiv-Component-Endo :
    (T : Component-Endo) → mere-equiv-Endo X (endo-Component-Endo T)
  mere-equiv-Component-Endo T = pr2 T

  canonical-Component-Endo : Component-Endo
  pr1 canonical-Component-Endo = X
  pr2 canonical-Component-Endo = refl-mere-equiv-Endo X

module _
  {l1 : Level} (X : Endo l1)
  where

  equiv-Component-Endo : (T S : Component-Endo X) → UU l1
  equiv-Component-Endo T S =
    equiv-Endo (endo-Component-Endo X T) (endo-Component-Endo X S)

  id-equiv-Component-Endo : (T : Component-Endo X) → equiv-Component-Endo T T
  id-equiv-Component-Endo T = id-equiv-Endo (endo-Component-Endo X T)

  equiv-eq-Component-Endo :
    (T S : Component-Endo X) → Id T S → equiv-Component-Endo T S
  equiv-eq-Component-Endo T .T refl = id-equiv-Component-Endo T
  
  is-contr-total-equiv-Component-Endo :
    is-contr
      ( Σ ( Component-Endo X)
          ( λ T → equiv-Component-Endo (canonical-Component-Endo X) T))
  is-contr-total-equiv-Component-Endo =
    is-contr-total-Eq-subtype
      ( is-contr-total-equiv-Endo X)
      ( λ Y → is-prop-type-trunc-Prop)
      ( X)
      ( id-equiv-Endo X)
      ( refl-mere-equiv-Endo X)

  is-equiv-equiv-eq-Component-Endo :
    (T : Component-Endo X) →
    is-equiv (equiv-eq-Component-Endo (canonical-Component-Endo X) T)
  is-equiv-equiv-eq-Component-Endo =
    fundamental-theorem-id
      ( canonical-Component-Endo X)
      ( id-equiv-Component-Endo (canonical-Component-Endo X))
      ( is-contr-total-equiv-Component-Endo)
      ( equiv-eq-Component-Endo (canonical-Component-Endo X))

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
  loop-space-Group (Cyclic lzero k) (ℤ-Mod-Cyclic k) (is-set-type-Ω-Cyclic k)

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
