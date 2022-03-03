---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-foundations.W-types where

open import foundation public
open import elementary-number-theory public

-- Theorem B.5.10



--------------------------------------------------------------------------------

-- Exercises

-- Exercise B.5

-- Exercise B.5 (a)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  -- We define the strict ordering on 𝕎 A B
  
  data _le-𝕎_ (x : 𝕎 A B) : 𝕎 A B → UU (l1 ⊔ l2) where
    le-∈-𝕎 : {y : 𝕎 A B} → x ∈-𝕎 y → x le-𝕎 y
    propagate-le-𝕎 : {y z : 𝕎 A B} → y ∈-𝕎 z → x le-𝕎 y → x le-𝕎 z

  -- The strict ordering is transitive, irreflexive, and asymmetric
  
  transitive-le-𝕎 : {x y z : 𝕎 A B} → y le-𝕎 z → x le-𝕎 y → x le-𝕎 z
  transitive-le-𝕎 {x = x} {y} {z} (le-∈-𝕎 H) K =
    propagate-le-𝕎 H K
  transitive-le-𝕎 {x = x} {y} {z} (propagate-le-𝕎 L H) K =
    propagate-le-𝕎 L (transitive-le-𝕎 H K)

  irreflexive-le-𝕎 :
    {x : 𝕎 A B} → ¬ (x le-𝕎 x)
  irreflexive-le-𝕎 {x = x} (le-∈-𝕎 H) = irreflexive-∈-𝕎 x H
  irreflexive-le-𝕎 {x = tree-𝕎 x α} (propagate-le-𝕎 (pair b refl) H) =
    irreflexive-le-𝕎 {x = α b} (transitive-le-𝕎 H (le-∈-𝕎 (pair b refl)))

  asymmetric-le-𝕎 :
    {x y : 𝕎 A B} → x le-𝕎 y → y le-𝕎 x → empty
  asymmetric-le-𝕎 H K = irreflexive-le-𝕎 (transitive-le-𝕎 H K)

-- Exercise B.5 (b)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (P : 𝕎 A B → UU l3)
  where
  
  -- We define an operation □-𝕎 that acts on families over 𝕎 A B.

  □-𝕎 : 𝕎 A B → UU (l1 ⊔ l2 ⊔ l3)
  □-𝕎 x = (y : 𝕎 A B) → (y le-𝕎 x) → P y

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {P : 𝕎 A B → UU l3}
  where

  -- The unit of □-𝕎 takes sections of P to sections of □-𝕎 P

  unit-□-𝕎 :
    ((x : 𝕎 A B) → P x) → ((x : 𝕎 A B) → □-𝕎 P x)
  unit-□-𝕎 f x y p = f y

  -- The reflector (counit) of □-𝕎 is dual, with an extra hypothesis

  reflect-□-𝕎 :
    ((x : 𝕎 A B) → □-𝕎 P x → P x) →
    ((x : 𝕎 A B) → □-𝕎 P x) → ((x : 𝕎 A B) → P x)
  reflect-□-𝕎 h f x = h x (f x)

  {- We first prove an intermediate induction principle with computation rule,
     where we obtain sections of □-𝕎 P. -}

  □-strong-ind-𝕎 :
    ((x : 𝕎 A B) → □-𝕎 P x → P x) → (x : 𝕎 A B) → □-𝕎 P x
  □-strong-ind-𝕎 h (tree-𝕎 x α) .(α b) (le-∈-𝕎 (pair b refl)) =
    h (α b) (□-strong-ind-𝕎 h (α b))
  □-strong-ind-𝕎 h (tree-𝕎 x α) y (propagate-le-𝕎 (pair b refl) K) =
    □-strong-ind-𝕎 h (α b) y K

  □-strong-comp-𝕎 :
    (h : (x : 𝕎 A B) → □-𝕎 P x → P x)
    (x : 𝕎 A B) (y : 𝕎 A B) (p : y le-𝕎 x) →
    Id (□-strong-ind-𝕎 h x y p) (h y (□-strong-ind-𝕎 h y))
  □-strong-comp-𝕎 h (tree-𝕎 x α) .(α b) (le-∈-𝕎 (pair b refl)) =
    refl
  □-strong-comp-𝕎 h (tree-𝕎 x α) y (propagate-le-𝕎 (pair b refl) K) =
    □-strong-comp-𝕎 h (α b) y K

{- Now we prove the actual induction principle with computation rule, where we
   obtain sections of P. -}

strong-ind-𝕎 :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (P : 𝕎 A B → UU l3) → 
  ((x : 𝕎 A B) → □-𝕎 P x → P x) → (x : 𝕎 A B) → P x
strong-ind-𝕎 P h = reflect-□-𝕎 h (□-strong-ind-𝕎 h)
                                               
strong-comp-𝕎 :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (P : 𝕎 A B → UU l3) →
  (h : (x : 𝕎 A B) → □-𝕎 P x → P x) (x : 𝕎 A B) →
  Id (strong-ind-𝕎 P h x) (h x (unit-□-𝕎 (strong-ind-𝕎 P h) x))
strong-comp-𝕎 P h x =
  ap (h x) (eq-htpy (λ y → eq-htpy (λ p → □-strong-comp-𝕎 h x y p)))

-- Exercise B.5 (c)

no-infinite-descent-𝕎 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (f : ℕ → 𝕎 A B) → ¬ ((n : ℕ) → (f (succ-ℕ n) le-𝕎 (f n)))
no-infinite-descent-𝕎 {A = A} {B} f =
  strong-ind-𝕎
    ( λ x → (f : ℕ → 𝕎 A B) (p : Id (f zero-ℕ) x) →
            ¬ ((n : ℕ) → (f (succ-ℕ n)) le-𝕎 (f n)))
    ( λ x IH f p H →
      IH ( f 1)
         ( tr (λ t → (f 1) le-𝕎 t) p (H zero-ℕ))
         ( f ∘ succ-ℕ)
         ( refl)
         ( λ n → H (succ-ℕ n)))
    ( f zero-ℕ)
    ( f)
    ( refl)

-- Exercise B.6

-- Exercise B.7

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  _≼-𝕎-Prop_ : 𝕎 A B → 𝕎 A B → UU-Prop (l1 ⊔ l2)
  (tree-𝕎 x α) ≼-𝕎-Prop (tree-𝕎 y β) =
    Π-Prop (B x) (λ b → exists-Prop (λ c → (α b) ≼-𝕎-Prop (β c)))

  _≼-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ≼-𝕎 y = type-Prop (x ≼-𝕎-Prop y)

  _≺-𝕎-Prop_ : 𝕎 A B → 𝕎 A B → UU-Prop (l1 ⊔ l2)
  x ≺-𝕎-Prop y =
    exists-Prop (λ (t : Σ (𝕎 A B) (λ w → w ∈-𝕎 y)) → x ≼-𝕎-Prop (pr1 t))

  _≺-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ≺-𝕎 y = type-Prop (x ≺-𝕎-Prop y)

  -- Exercise B.7 (a)

  refl-≼-𝕎 : (x : 𝕎 A B) → x ≼-𝕎 x
  refl-≼-𝕎 (tree-𝕎 x α) b = unit-trunc-Prop (pair b (refl-≼-𝕎 (α b)))

  transitive-≼-𝕎 : {x y z : 𝕎 A B} → (x ≼-𝕎 y) → (y ≼-𝕎 z) → (x ≼-𝕎 z)
  transitive-≼-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} {tree-𝕎 z γ} H K a =
    apply-universal-property-trunc-Prop
      ( H a)
      ( exists-Prop (λ c → (α a) ≼-𝕎-Prop (γ c)))
      ( λ t →
        apply-universal-property-trunc-Prop
          ( K (pr1 t))
          ( exists-Prop (λ c → (α a) ≼-𝕎-Prop (γ c)))
          ( λ s →
            unit-trunc-Prop
              ( pair
                ( pr1 s)
                ( transitive-≼-𝕎
                  { α a}
                  { β (pr1 t)}
                  { γ (pr1 s)}
                  ( pr2 t)
                  ( pr2 s)))))

  -- Exercise B.7 (a) (i)

  _strong-≼-𝕎-Prop_ : 𝕎 A B → 𝕎 A B → UU-Prop (l1 ⊔ l2)
  x strong-≼-𝕎-Prop y =
    Π-Prop
      ( 𝕎 A B)
      ( λ u →
        Π-Prop
          ( u ∈-𝕎 x)
          ( λ H →
            exists-Prop
              ( λ (v : 𝕎 A B) →
                exists-Prop (λ (K : v ∈-𝕎 y) → u ≼-𝕎-Prop v))))

  _strong-≼-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x strong-≼-𝕎 y = type-Prop (x strong-≼-𝕎-Prop y)

  strong-≼-≼-𝕎 : {x y : 𝕎 A B} → (x ≼-𝕎 y) → (x strong-≼-𝕎 y)
  strong-≼-≼-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} H .(α b) (pair b refl) =
    apply-universal-property-trunc-Prop (H b)
      ( exists-Prop ((λ v → exists-Prop (λ hv → (α b) ≼-𝕎-Prop v))))
      ( f)
      where
      f : Σ (B y) (λ c → pr1 (α b ≼-𝕎-Prop β c)) →
          exists (λ v → exists-Prop (λ hv → α b ≼-𝕎-Prop v))
      f (pair c K) =
        intro-exists
          ( λ v → exists-Prop (λ hv → α b ≼-𝕎-Prop v))
          ( β c)
          ( intro-exists
            ( λ hβc → α b ≼-𝕎-Prop β c)
            ( pair c refl)
            ( K))

  ≼-strong-≼-𝕎 : {x y : 𝕎 A B} → (x strong-≼-𝕎 y) → (x ≼-𝕎 y)
  ≼-strong-≼-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} H b =
    apply-universal-property-trunc-Prop
      ( H (α b) (pair b refl))
      ( exists-Prop (λ c → α b ≼-𝕎-Prop β c))
      ( f)
    where
    f : Σ ( 𝕎 A B) (λ v → exists (λ K → α b ≼-𝕎-Prop v)) →
        exists (λ c → α b ≼-𝕎-Prop β c)
    f (pair v K) =
        apply-universal-property-trunc-Prop K
          ( exists-Prop (λ c → α b ≼-𝕎-Prop β c))
          ( g)
      where
      g : (v ∈-𝕎 tree-𝕎 y β) × (α b ≼-𝕎 v) → ∃ (λ c → α b ≼-𝕎 β c)
      g (pair (pair c p) M) = intro-∃ c (tr (λ t → α b ≼-𝕎 t) (inv p) M)

  -- Exercise B.7 (a) (ii)

  ≼-∈-𝕎 : {x y : 𝕎 A B} → (x ∈-𝕎 y) → (x ≼-𝕎 y)
  ≼-∈-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} (pair v p) u =
    intro-exists
      ( λ z → α u ≼-𝕎-Prop β z)
      ( v)
      ( tr ( λ t → α u ≼-𝕎 t)
           ( inv p)
           ( ≼-∈-𝕎 {α u} {tree-𝕎 x α} (pair u refl)))

  ≼-le-𝕎 : {x y : 𝕎 A B} → (x le-𝕎 y) → (x ≼-𝕎 y)
  ≼-le-𝕎 {x} {y} (le-∈-𝕎 H) = ≼-∈-𝕎 H
  ≼-le-𝕎 {x} {y} (propagate-le-𝕎 {y = y'} K H) =
    transitive-≼-𝕎 {x} {y = y'} {y} (≼-le-𝕎 H) (≼-∈-𝕎 K)

  -- Exercise B.7 (a) (iii)

  not-≼-∈-𝕎 : {x y : 𝕎 A B} → (x ∈-𝕎 y) → ¬ (y ≼-𝕎 x)
  not-≼-∈-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} (pair b p) K =
    apply-universal-property-trunc-Prop (K b) (empty-Prop) f
    where
    f : Σ (B x) (λ c → β b ≼-𝕎 α c) → empty
    f (pair c L) =
      not-≼-∈-𝕎 {α c} {β b} (tr (λ t → α c ∈-𝕎 t) (inv p) (pair c refl)) L

  not-≼-le-𝕎 : {x y : 𝕎 A B} → (x le-𝕎 y) → ¬ (y ≼-𝕎 x)
  not-≼-le-𝕎 {x} {y} (le-∈-𝕎 H) = not-≼-∈-𝕎 {x} {y} H
  not-≼-le-𝕎 {x} {y} (propagate-le-𝕎 {y = y'} H K) L =
    not-≼-∈-𝕎 {y'} {y} H (transitive-≼-𝕎 {y} {x} {y'} L (≼-le-𝕎 K))

  -- Exercise B.7 (a) (iv)

  is-least-≼-constant-𝕎 :
    {x : A} (h : is-empty (B x)) (w : 𝕎 A B) → constant-𝕎 x h ≼-𝕎 w
  is-least-≼-constant-𝕎 h (tree-𝕎 y β) x = ex-falso (h x)

  is-least-≼-is-constant-𝕎 :
    {x : 𝕎 A B} → is-constant-𝕎 x → (y : 𝕎 A B) → x ≼-𝕎 y
  is-least-≼-is-constant-𝕎 {tree-𝕎 x α} H (tree-𝕎 y β) z =
    ex-falso (H z)

  is-constant-is-least-≼-𝕎 :
    {x : 𝕎 A B} → ((y : 𝕎 A B) → x ≼-𝕎 y) → is-constant-𝕎 x
  is-constant-is-least-≼-𝕎 {tree-𝕎 x α} H b =
    not-≼-∈-𝕎 {α b} {tree-𝕎 x α} (pair b refl) (H (α b))

  -- Exercise B.7 (b)

  ≼-≺-𝕎 : {x y : 𝕎 A B} → (x ≺-𝕎 y) → (x ≼-𝕎 y)
  ≼-≺-𝕎 {x} {y} H =
    apply-universal-property-trunc-Prop H (x ≼-𝕎-Prop y) f
    where
    f : Σ (Σ (𝕎 A B) (λ w → w ∈-𝕎 y)) (λ t → x ≼-𝕎 pr1 t) → (x ≼-𝕎 y)
    f (pair (pair w K) L) = transitive-≼-𝕎 {x} {w} {y} L (≼-∈-𝕎 K)

  transitive-≺-𝕎 : {x y z : 𝕎 A B} → (x ≺-𝕎 y) → (y ≺-𝕎 z) → (x ≺-𝕎 z)
  transitive-≺-𝕎 {x} {y} {z} H K =
    apply-universal-property-trunc-Prop H (x ≺-𝕎-Prop z) f
    where
    f : Σ (Σ (𝕎 A B) (λ w → w ∈-𝕎 y)) (λ t → x ≼-𝕎 pr1 t) → x ≺-𝕎 z
    f (pair (pair w L) M) =
      apply-universal-property-trunc-Prop K (x ≺-𝕎-Prop z) g
      where
      g : Σ (Σ (𝕎 A B) (λ w → w ∈-𝕎 z)) (λ t → y ≼-𝕎 pr1 t) → x ≺-𝕎 z
      g (pair (pair v P) Q) =
        intro-exists
          ( λ (t : Σ (𝕎 A B) (λ s → s ∈-𝕎 z)) → x ≼-𝕎-Prop (pr1 t))
          ( pair v P)
          ( transitive-≼-𝕎 {x} {w} {v} M
            ( transitive-≼-𝕎 {w} {y} {v} (≼-∈-𝕎 L) Q))

  irreflexive-≺-𝕎 : {x : 𝕎 A B} → ¬ (x ≺-𝕎 x)
  irreflexive-≺-𝕎 {tree-𝕎 x α} H =
    apply-universal-property-trunc-Prop H empty-Prop f
    where
    f : ¬ ( Σ ( Σ (𝕎 A B) (λ w → w ∈-𝕎 tree-𝕎 x α))
              ( λ t → tree-𝕎 x α ≼-𝕎 pr1 t))
    f (pair (pair w K) L) = not-≼-∈-𝕎 {w} {tree-𝕎 x α} K L

  in-lower-set-≺-𝕎-Prop : (x y : 𝕎 A B) → UU-Prop (l1 ⊔ l2)
  in-lower-set-≺-𝕎-Prop x y = y ≺-𝕎-Prop x

  in-lower-set-≺-𝕎 : (x y : 𝕎 A B) → UU (l1 ⊔ l2)
  in-lower-set-≺-𝕎 x y = y ≺-𝕎 x

  has-same-lower-set-≺-𝕎 : (x y : 𝕎 A B) → UU (l1 ⊔ l2)
  has-same-lower-set-≺-𝕎 x y = (z : 𝕎 A B) → (z ≺-𝕎 x) × (z ≺-𝕎 y)

  _≈-𝕎-Prop_ : (x y : 𝕎 A B) → UU-Prop (l1 ⊔ l2)
  x ≈-𝕎-Prop y = prod-Prop (x ≼-𝕎-Prop y) (y ≼-𝕎-Prop x)

  _≈-𝕎_ : (x y : 𝕎 A B) → UU (l1 ⊔ l2)
  x ≈-𝕎 y = type-Prop (x ≈-𝕎-Prop y)

{-
  ≈-has-same-lower-set-≺-𝕎 :
    {x y : 𝕎 A B} → has-same-lower-set-≺-𝕎 x y → x ≈-𝕎 y
  ≈-has-same-lower-set-≺-𝕎 {x} {y} H = {!!}
-}

--------------------------------------------------------------------------------

data _leq-𝕎_ {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (x : 𝕎 A B) :
  𝕎 A B → UU (l1 ⊔ l2) where
  refl-leq-𝕎 : x leq-𝕎 x
  propagate-leq-𝕎 : {y z : 𝕎 A B} → y ∈-𝕎 z → x leq-𝕎 y → x leq-𝕎 z

--------------------------------------------------------------------------------

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  data Path-𝕎 : 𝕎 A B → UU (l1 ⊔ l2) where
    root : (w : 𝕎 A B) → Path-𝕎 w
    cons : (a : A) (f : B a → 𝕎 A B) (b : B a) → Path-𝕎 (f b) → Path-𝕎 (tree-𝕎 a f)

  length-Path-𝕎 : (w : 𝕎 A B) → Path-𝕎 w → ℕ
  length-Path-𝕎 w (root .w) = zero-ℕ
  length-Path-𝕎 .(tree-𝕎 a f) (cons a f b p) = succ-ℕ (length-Path-𝕎 (f b) p)
```
