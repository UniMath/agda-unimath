# The circle

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.circle where

open import foundation.connected-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.universal-property-propositional-truncation
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

```agda
free-loop : {l1 : Level} (X : UU l1) → UU l1
free-loop X = Σ X (λ x → Id x x)

module _
  {l1 : Level} {X : UU l1}
  where
    
  base-free-loop : free-loop X → X
  base-free-loop = pr1
  
  loop-free-loop : (α : free-loop X) → Id (base-free-loop α) (base-free-loop α)
  loop-free-loop = pr2

-- Now we characterize the identity types of free loops

module _
  {l1 : Level} {X : UU l1}
  where

  Eq-free-loop : (α α' : free-loop X) → UU l1
  Eq-free-loop (pair x α) α' =
    Σ (Id x (pr1 α')) (λ p → Id (α ∙ p) (p ∙ (pr2 α')))

  refl-Eq-free-loop : (α : free-loop X) → Eq-free-loop α α
  pr1 (refl-Eq-free-loop (pair x α)) = refl
  pr2 (refl-Eq-free-loop (pair x α)) = right-unit

  Eq-eq-free-loop : (α α' : free-loop X) → Id α α' → Eq-free-loop α α'
  Eq-eq-free-loop α .α refl = refl-Eq-free-loop α

  abstract
    is-contr-total-Eq-free-loop :
      (α : free-loop X) → is-contr (Σ (free-loop X) (Eq-free-loop α))
    is-contr-total-Eq-free-loop (pair x α) =
      is-contr-total-Eq-structure
        ( λ x α' p → Id (α ∙ p) (p ∙ α'))
        ( is-contr-total-path x)
        ( pair x refl)
        ( is-contr-is-equiv'
          ( Σ (Id x x) (λ α' → Id α α'))
          ( tot (λ α' α → right-unit ∙ α))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ α' → is-equiv-concat right-unit α'))
          ( is-contr-total-path α))

  abstract
    is-equiv-Eq-eq-free-loop :
      (α α' : free-loop X) → is-equiv (Eq-eq-free-loop α α')
    is-equiv-Eq-eq-free-loop α =
      fundamental-theorem-id α
        ( refl-Eq-free-loop α)
        ( is-contr-total-Eq-free-loop α)
        ( Eq-eq-free-loop α) 

{- We introduce dependent free loops, which are used in the induction principle
   of the circle. -}

module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (P : X → UU l2)
  where
    
  dependent-free-loop : UU l2
  dependent-free-loop =
    Σ ( P (base-free-loop α))
      ( λ p₀ → Id (tr P (loop-free-loop α) p₀) p₀)

  Eq-dependent-free-loop : (p p' : dependent-free-loop) → UU l2
  Eq-dependent-free-loop (pair y p) p' =
    Σ ( Id y (pr1 p'))
      ( λ q → Id (p ∙ q) ((ap (tr P (loop-free-loop α)) q) ∙ (pr2 p')))

  refl-Eq-dependent-free-loop :
    (p : dependent-free-loop) → Eq-dependent-free-loop p p
  pr1 (refl-Eq-dependent-free-loop (pair y p)) = refl
  pr2 (refl-Eq-dependent-free-loop (pair y p)) = right-unit

  Eq-dependent-free-loop-eq :
    ( p p' : dependent-free-loop) → Id p p' → Eq-dependent-free-loop p p'
  Eq-dependent-free-loop-eq p .p refl = refl-Eq-dependent-free-loop p

  abstract
    is-contr-total-Eq-dependent-free-loop :
      ( p : dependent-free-loop) →
      is-contr (Σ dependent-free-loop (Eq-dependent-free-loop p))
    is-contr-total-Eq-dependent-free-loop (pair y p) =
      is-contr-total-Eq-structure
        ( λ y' p' q → Id (p ∙ q) ((ap (tr P (loop-free-loop α)) q) ∙ p'))
        ( is-contr-total-path y)
        ( pair y refl)
        ( is-contr-is-equiv'
          ( Σ (Id (tr P (loop-free-loop α) y) y) (λ p' → Id p p'))
          ( tot (λ p' α → right-unit ∙ α))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ p' → is-equiv-concat right-unit p'))
          ( is-contr-total-path p))

  abstract
    is-equiv-Eq-dependent-free-loop-eq :
      (p p' : dependent-free-loop) →
      is-equiv (Eq-dependent-free-loop-eq p p')
    is-equiv-Eq-dependent-free-loop-eq p =
      fundamental-theorem-id p
        ( refl-Eq-dependent-free-loop p)
        ( is-contr-total-Eq-dependent-free-loop p)
        ( Eq-dependent-free-loop-eq p)

  eq-Eq-dependent-free-loop :
    (p p' : dependent-free-loop) →
    Eq-dependent-free-loop p p' → Id p p'
  eq-Eq-dependent-free-loop p p' =
    map-inv-is-equiv (is-equiv-Eq-dependent-free-loop-eq p p')

{- We now define the induction principle of the circle. -}

module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (P : X → UU l2)
  where

  ev-free-loop' : ((x : X) → P x) → dependent-free-loop α P
  pr1 (ev-free-loop' f) = f (base-free-loop α)
  pr2 (ev-free-loop' f) = apd f (loop-free-loop α)

module _
  {l1 : Level} (l2 : Level) {X : UU l1} (α : free-loop X)
  where

  induction-principle-circle : UU ((lsuc l2) ⊔ l1)
  induction-principle-circle = (P : X → UU l2) → sec (ev-free-loop' α P)

{- Section 11.2 The universal property of the circle -}

{- We first state the universal property of the circle -}

module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (Y : UU l2)
  where

  ev-free-loop : (X → Y) → free-loop Y
  ev-free-loop f = pair (f (base-free-loop α)) (ap f (loop-free-loop α))

module _
  {l1 : Level} (l2 : Level) {X : UU l1} (α : free-loop X)
  where
  
  universal-property-circle : UU (l1 ⊔ lsuc l2)
  universal-property-circle = (Y : UU l2) → is-equiv (ev-free-loop α Y)

{- A fairly straightforward proof of the universal property of the circle
   factors through the dependent universal property of the circle. -}

module _
  {l1 : Level} (l2 : Level) {X : UU l1} (α : free-loop X)
  where

  dependent-universal-property-circle : UU ((lsuc l2) ⊔ l1)
  dependent-universal-property-circle =
    (P : X → UU l2) → is-equiv (ev-free-loop' α P)

{- We first prove that the dependent universal property of the circle follows
   from the induction principle of the circle. To show this, we have to show
   that the section of ev-free-loop' is also a retraction. This construction
   is also by the induction principle of the circle, but it requires (a minimal
   amount of) preparations. -}

module _
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} (f g : (x : X) → P x)
  where

  Eq-subst : X → UU _
  Eq-subst x = Id (f x) (g x)

  tr-Eq-subst :
    { x y : X} (p : Id x y) (q : Eq-subst x) (r : Eq-subst y)→
    ( Id ((apd f p) ∙ r) ((ap (tr P p) q) ∙ (apd g p))) →
    ( Id (tr Eq-subst p q) r)
  tr-Eq-subst refl q .((ap id q) ∙ refl) refl = inv (right-unit ∙ (ap-id q))

module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  dependent-free-loop-htpy :
    {l2 : Level} {P : X → UU l2} {f g : (x : X) → P x} →
    ( Eq-dependent-free-loop α P (ev-free-loop' α P f) (ev-free-loop' α P g)) →
    ( dependent-free-loop α (λ x → Id (f x) (g x)))
  dependent-free-loop-htpy {l2} {P} {f} {g} (pair p q) =
    pair p (tr-Eq-subst f g (loop-free-loop α) p p q)

  isretr-ind-circle :
    ( ind-circle : {l : Level} → induction-principle-circle l α)
    { l2 : Level} (P : X → UU l2) →
    ( (pr1 (ind-circle P)) ∘ (ev-free-loop' α P)) ~ id
  isretr-ind-circle ind-circle P f =
    eq-htpy
      ( pr1
        ( ind-circle
          ( λ t → Id (pr1 (ind-circle P) (ev-free-loop' α P f) t) (f t)))
        ( dependent-free-loop-htpy
          ( Eq-dependent-free-loop-eq α P _ _
            ( pr2 (ind-circle P) (ev-free-loop' α P f)))))

  abstract
    dependent-universal-property-induction-principle-circle :
      ({l : Level} → induction-principle-circle l α) →
      ({l : Level} → dependent-universal-property-circle l α)
    dependent-universal-property-induction-principle-circle ind-circle P =
      is-equiv-has-inverse
        ( pr1 (ind-circle P))
        ( pr2 (ind-circle P))
        ( isretr-ind-circle ind-circle P)

  {- We use the dependent universal property to derive a uniqeness property of
     dependent functions on the circle. -}

  uniqueness-dependent-universal-property-circle :
    ({l : Level} → dependent-universal-property-circle l α) →
    {l2 : Level} {P : X → UU l2} (k : dependent-free-loop α P) →
    is-contr
      ( Σ ( (x : X) → P x)
          ( λ h → Eq-dependent-free-loop α P (ev-free-loop' α P h) k))
  uniqueness-dependent-universal-property-circle dup-circle {l2} {P} k =
    is-contr-is-equiv'
      ( fib (ev-free-loop' α P) k)
      ( tot (λ h → Eq-dependent-free-loop-eq α P (ev-free-loop' α P h) k))
      ( is-equiv-tot-is-fiberwise-equiv
        (λ h → is-equiv-Eq-dependent-free-loop-eq α P (ev-free-loop' α P h) k))
      ( is-contr-map-is-equiv (dup-circle P) k)

{- Now that we have established the dependent universal property, we can
   reduce the (non-dependent) universal property to the dependent case. We do
   so by constructing a commuting triangle relating ev-free-loop to 
   ev-free-loop' via a comparison equivalence. -}

tr-const :
  {i j : Level} {A : UU i} {B : UU j} {x y : A} (p : Id x y) (b : B) →
  Id (tr (λ (a : A) → B) p b) b
tr-const refl b = refl

apd-const :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A}
  (p : Id x y) → Id (apd f p) ((tr-const p (f x)) ∙ (ap f p))
apd-const f refl = refl

module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (Y : UU l2)
  where

  compute-dependent-free-loop-const :
    free-loop Y ≃ dependent-free-loop α (λ x → Y)
  compute-dependent-free-loop-const =
    equiv-tot (λ y → equiv-concat (tr-const (loop-free-loop α) y) y)

  map-compute-dependent-free-loop-const :
    free-loop Y → dependent-free-loop α (λ x → Y)
  map-compute-dependent-free-loop-const =
    map-equiv compute-dependent-free-loop-const

  triangle-comparison-free-loop :
    ( map-compute-dependent-free-loop-const ∘ (ev-free-loop α Y)) ~
    ( ev-free-loop' α (λ x → Y))
  triangle-comparison-free-loop f =
    eq-Eq-dependent-free-loop α
      ( λ x → Y)
      ( map-compute-dependent-free-loop-const
        ( ev-free-loop α Y f))
      ( ev-free-loop' α (λ x → Y) f)
      ( pair refl (right-unit ∙ (inv (apd-const f (loop-free-loop α)))))

module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  abstract
    universal-property-dependent-universal-property-circle :
      ({l : Level} → dependent-universal-property-circle l α) →
      ({l : Level} → universal-property-circle l α)
    universal-property-dependent-universal-property-circle dup-circle Y =
      is-equiv-right-factor
        ( ev-free-loop' α (λ x → Y))
        ( map-compute-dependent-free-loop-const α Y)
        ( ev-free-loop α Y)
        ( inv-htpy (triangle-comparison-free-loop α Y))
        ( is-equiv-map-equiv (compute-dependent-free-loop-const α Y))
        ( dup-circle (λ x → Y))

  {- Now we get the universal property of the circle from the induction
     principle of the circle by composing the earlier two proofs. -}

  abstract
    universal-property-induction-principle-circle :
      ({l : Level} → induction-principle-circle l α) →
      ({l : Level} → universal-property-circle l α)
    universal-property-induction-principle-circle X =
      universal-property-dependent-universal-property-circle
        ( dependent-universal-property-induction-principle-circle α X)

  abstract
    uniqueness-universal-property-circle :
      ({l : Level} → universal-property-circle l α) →
      {l2 : Level} (Y : UU l2) (α' : free-loop Y) →
      is-contr (Σ (X → Y) (λ f → Eq-free-loop (ev-free-loop α Y f) α'))
    uniqueness-universal-property-circle up-circle Y α' =
      is-contr-is-equiv'
        ( fib (ev-free-loop α Y) α')
        ( tot (λ f → Eq-eq-free-loop (ev-free-loop α Y f) α'))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ f → is-equiv-Eq-eq-free-loop (ev-free-loop α Y f) α'))
        ( is-contr-map-is-equiv (up-circle Y) α')

{- We assume that we have a circle. -}

postulate 𝕊¹ : UU lzero

postulate base-𝕊¹ : 𝕊¹

postulate loop-𝕊¹ : Id base-𝕊¹ base-𝕊¹

free-loop-𝕊¹ : free-loop 𝕊¹
pr1 free-loop-𝕊¹ = base-𝕊¹
pr2 free-loop-𝕊¹ = loop-𝕊¹

𝕊¹-Pointed-Type : Pointed-Type lzero
pr1 𝕊¹-Pointed-Type = 𝕊¹
pr2 𝕊¹-Pointed-Type = base-𝕊¹

postulate ind-𝕊¹ : {l : Level} → induction-principle-circle l free-loop-𝕊¹

module _
  where
  
  dependent-universal-property-𝕊¹ :
    {l : Level} → dependent-universal-property-circle l free-loop-𝕊¹
  dependent-universal-property-𝕊¹ =
    dependent-universal-property-induction-principle-circle free-loop-𝕊¹ ind-𝕊¹

  uniqueness-dependent-universal-property-𝕊¹ :
    {l : Level} {P : 𝕊¹ → UU l} (k : dependent-free-loop free-loop-𝕊¹ P) →
    is-contr
      ( Σ ( (x : 𝕊¹) → P x)
          ( λ h →
            Eq-dependent-free-loop free-loop-𝕊¹ P
              ( ev-free-loop' free-loop-𝕊¹ P h) k))
  uniqueness-dependent-universal-property-𝕊¹ {l} {P} =
    uniqueness-dependent-universal-property-circle
      free-loop-𝕊¹
      dependent-universal-property-𝕊¹

  module _
    {l : Level} (P : 𝕊¹ → UU l) (p0 : P base-𝕊¹) (α : Id (tr P loop-𝕊¹ p0) p0)
    where

    Π-𝕊¹ : UU l
    Π-𝕊¹ =
      Σ ( (x : 𝕊¹) → P x)
        ( λ h →
          Eq-dependent-free-loop free-loop-𝕊¹ P
            ( ev-free-loop' free-loop-𝕊¹ P h) (pair p0 α))

    apply-dependent-universal-property-𝕊¹ : Π-𝕊¹
    apply-dependent-universal-property-𝕊¹ =
      center (uniqueness-dependent-universal-property-𝕊¹ (pair p0 α))
  
    function-apply-dependent-universal-property-𝕊¹ : (x : 𝕊¹) → P x
    function-apply-dependent-universal-property-𝕊¹ =
      pr1 apply-dependent-universal-property-𝕊¹

    base-dependent-universal-property-𝕊¹ :
      Id (function-apply-dependent-universal-property-𝕊¹ base-𝕊¹) p0
    base-dependent-universal-property-𝕊¹ =
      pr1 (pr2 apply-dependent-universal-property-𝕊¹)

    loop-dependent-universal-property-𝕊¹ :
      Id ( apd function-apply-dependent-universal-property-𝕊¹ loop-𝕊¹ ∙
           base-dependent-universal-property-𝕊¹)
         ( ap (tr P loop-𝕊¹) base-dependent-universal-property-𝕊¹ ∙ α)
    loop-dependent-universal-property-𝕊¹ =
      pr2 (pr2 apply-dependent-universal-property-𝕊¹)

  universal-property-𝕊¹ :
    {l : Level} → universal-property-circle l free-loop-𝕊¹
  universal-property-𝕊¹ =
    universal-property-dependent-universal-property-circle
      free-loop-𝕊¹
      dependent-universal-property-𝕊¹

  uniqueness-universal-property-𝕊¹ :
    {l : Level} {X : UU l} (α : free-loop X) →
    is-contr
      ( Σ ( 𝕊¹ → X)
          ( λ h → Eq-free-loop (ev-free-loop free-loop-𝕊¹ X h) α))
  uniqueness-universal-property-𝕊¹ {l} {X} =
    uniqueness-universal-property-circle free-loop-𝕊¹ universal-property-𝕊¹ X

  module _
    {l : Level} {X : UU l} (x : X) (α : Id x x)
    where

    Map-𝕊¹ : UU l
    Map-𝕊¹ =
      Σ ( 𝕊¹ → X)
        ( λ h → Eq-free-loop (ev-free-loop free-loop-𝕊¹ X h) (pair x α))

    apply-universal-property-𝕊¹ : Map-𝕊¹
    apply-universal-property-𝕊¹ =
      center (uniqueness-universal-property-𝕊¹ (pair x α))
      
    map-apply-universal-property-𝕊¹ : 𝕊¹ → X
    map-apply-universal-property-𝕊¹ =
      pr1 apply-universal-property-𝕊¹

    base-universal-property-𝕊¹ :
      Id (map-apply-universal-property-𝕊¹ base-𝕊¹) x
    base-universal-property-𝕊¹ =
      pr1 (pr2 apply-universal-property-𝕊¹)

    loop-universal-property-𝕊¹ :
      Id ( ap map-apply-universal-property-𝕊¹ loop-𝕊¹ ∙
           base-universal-property-𝕊¹)
         ( base-universal-property-𝕊¹ ∙ α)
    loop-universal-property-𝕊¹ =
      pr2 (pr2 apply-universal-property-𝕊¹)

{- Exercises -}

-- Exercise 11.1

{- The dependent universal property of the circle (and hence also the induction
   principle of the circle, implies that the circle is connected in the sense
   that for any family of propositions parametrized by the circle, if the
   proposition at the base holds, then it holds for any x : circle. -}

abstract
  is-connected-circle' :
    { l1 l2 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : dependent-universal-property-circle l2 l)
    ( P : X → UU l2) (is-prop-P : (x : X) → is-prop (P x)) →
    P (base-free-loop l) → (x : X) → P x
  is-connected-circle' l dup-circle P is-prop-P p =
    map-inv-is-equiv
      ( dup-circle P)
      ( pair p (center (is-prop-P _ (tr P (pr2 l) p) p)))

--------------------------------------------------------------------------------

-- The circle is path connected

mere-eq-𝕊¹ : (x y : 𝕊¹) → mere-eq x y
mere-eq-𝕊¹ =
  function-apply-dependent-universal-property-𝕊¹
    ( λ x → (y : 𝕊¹) → mere-eq x y)
    ( function-apply-dependent-universal-property-𝕊¹
      ( mere-eq base-𝕊¹)
      ( refl-mere-eq)
      ( eq-is-prop is-prop-type-trunc-Prop))
    ( eq-is-prop (is-prop-Π (λ y → is-prop-type-trunc-Prop)))

is-path-connected-𝕊¹ : is-path-connected 𝕊¹
is-path-connected-𝕊¹ = is-path-connected-mere-eq base-𝕊¹ (mere-eq-𝕊¹ base-𝕊¹)
```
