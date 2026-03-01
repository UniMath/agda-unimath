# Simplices

```agda
module simplicial-type-theory.simplices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.commuting-triangles-of-homotopies
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import order-theory.bounded-total-orders
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.preorders

open import orthogonal-factorization-systems.extensions-maps
open import orthogonal-factorization-systems.types-local-at-maps

open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Goals

Formalize

- comp-is-segal
- witness-comp-is-segal
- uniqueness-comp-is-segal
- is-segal-function-type
- trivial identities
- associativity of comp-is-segal

## Definitions

```agda
module simplex
  {l1 : Level} (I : Bounded-Total-Order l1 l1)
  where

  mutual
  
    data
      Δ : ℕ → UU l1
      where
      
      pt-Δ : Δ 0

      cons-Δ :
        {n : ℕ} (x : Δ n) (i : type-Bounded-Total-Order I) →
        (H : leq-Bounded-Total-Order I i (final-Δ x)) → Δ (succ-ℕ n)

    final-Δ : {n : ℕ} → Δ n → type-Bounded-Total-Order I
    final-Δ pt-Δ = top-Bounded-Total-Order I
    final-Δ (cons-Δ x i H) = i

  data
    functional-Δ-0 : UU l1
    where
    pt-functional-Δ-0 : functional-Δ-0

  is-contr-functional-Δ-0 : is-contr functional-Δ-0
  pr1 is-contr-functional-Δ-0 = pt-functional-Δ-0
  pr2 is-contr-functional-Δ-0 pt-functional-Δ-0 = refl

  leq-functional-Δ-0 : functional-Δ-0 → functional-Δ-0 → UU l1
  leq-functional-Δ-0 x y = functional-Δ-0

  leq-prop-functional-Δ-0 :
    functional-Δ-0 → functional-Δ-0 → Prop l1
  pr1 (leq-prop-functional-Δ-0 x y) = leq-functional-Δ-0 x y
  pr2 (leq-prop-functional-Δ-0 x y) = is-prop-is-contr is-contr-functional-Δ-0

  refl-leq-functional-Δ-0 : is-reflexive leq-functional-Δ-0
  refl-leq-functional-Δ-0 x = pt-functional-Δ-0

  transitive-leq-functional-Δ-0 : is-transitive leq-functional-Δ-0
  transitive-leq-functional-Δ-0 x y z H K = pt-functional-Δ-0

  antisymmetric-leq-functional-Δ-0 : is-antisymmetric leq-functional-Δ-0
  antisymmetric-leq-functional-Δ-0
    pt-functional-Δ-0 pt-functional-Δ-0 pt-functional-Δ-0 pt-functional-Δ-0 =
    refl

  functional-Δ-0-Preorder : Preorder l1 l1
  pr1 functional-Δ-0-Preorder = functional-Δ-0
  pr1 (pr2 functional-Δ-0-Preorder) = leq-prop-functional-Δ-0
  pr1 (pr2 (pr2 functional-Δ-0-Preorder)) = refl-leq-functional-Δ-0
  pr2 (pr2 (pr2 functional-Δ-0-Preorder)) = transitive-leq-functional-Δ-0
  
  functional-Δ-0-Poset : Poset l1 l1
  pr1 functional-Δ-0-Poset = functional-Δ-0-Preorder
  pr2 functional-Δ-0-Poset = antisymmetric-leq-functional-Δ-0

  functional-Δ-Poset : ℕ → Poset l1 l1
  functional-Δ-Poset zero-ℕ =
    functional-Δ-0-Poset
  functional-Δ-Poset (succ-ℕ n) =
    hom-poset-Poset (functional-Δ-Poset n) (poset-Bounded-Total-Order I)

  functional-Δ : ℕ → UU l1
  functional-Δ n = type-Poset (functional-Δ-Poset n)

  ap-cons-Δ :
    {n : ℕ} {x y : Δ n} (p : x ＝ y)
    {i j : type-Bounded-Total-Order I} (q : i ＝ j) →
    (H : leq-Bounded-Total-Order I i (final-Δ x)) →
    (K : leq-Bounded-Total-Order I j (final-Δ y)) →
    cons-Δ x i H ＝ cons-Δ y j K
  ap-cons-Δ refl refl H K =
    ap (cons-Δ _ _) (eq-is-prop (is-prop-leq-Bounded-Total-Order I _ _))

  initial-Δ : (n : ℕ) → Δ (n +ℕ 1) → Δ n
  initial-Δ n (cons-Δ x i H) = x
    
  data
    Eq-Δ : (n : ℕ) → Δ n → Δ n → UU l1
    where

    refl-Eq-pt-Δ : Eq-Δ 0 pt-Δ pt-Δ

    Eq-cons-Δ :
      {n : ℕ} {x y : Δ n} {i j : type-Bounded-Total-Order I} →
      (H : leq-Bounded-Total-Order I i (final-Δ x)) →
      (K : leq-Bounded-Total-Order I j (final-Δ y)) →
      Eq-Δ n x y → i ＝ j → Eq-Δ (succ-ℕ n) (cons-Δ x i H) (cons-Δ y j K)

  refl-Eq-Δ :
    {n : ℕ} → is-reflexive (Eq-Δ n)
  refl-Eq-Δ pt-Δ = refl-Eq-pt-Δ
  refl-Eq-Δ (cons-Δ x i H) =
    Eq-cons-Δ H H (refl-Eq-Δ x) refl

  Eq-eq-Δ :
    (n : ℕ) (x y : Δ n) → x ＝ y → Eq-Δ n x y
  Eq-eq-Δ n x y refl = refl-Eq-Δ x

  eq-Eq-Δ :
    {n : ℕ} {x y : Δ n} → Eq-Δ n x y → x ＝ y
  eq-Eq-Δ refl-Eq-pt-Δ = refl
  eq-Eq-Δ (Eq-cons-Δ H K e refl) =
    ap-cons-Δ (eq-Eq-Δ e) refl H K

  in-Δ : type-Bounded-Total-Order I → Δ 1
  in-Δ i = cons-Δ pt-Δ i (is-top-element-top-Bounded-Total-Order I _)

  is-section-in-Δ : is-section final-Δ in-Δ
  is-section-in-Δ i = refl

  is-retraction-in-Δ : is-retraction final-Δ in-Δ
  is-retraction-in-Δ (cons-Δ pt-Δ i H) =
    ap-cons-Δ refl refl _ H

  is-equiv-in-Δ : is-equiv (final-Δ {1})
  is-equiv-in-Δ =
    is-equiv-is-invertible
      in-Δ
      is-section-in-Δ
      is-retraction-in-Δ

  d00 : Δ 0 → Δ 1
  d00 pt-Δ = in-Δ (top-Bounded-Total-Order I)

  d01 : Δ 0 → Δ 1
  d01 pt-Δ = in-Δ (bottom-Bounded-Total-Order I)

  d10 : Δ 1 → Δ 2
  d10 (cons-Δ pt-Δ i H) =
    cons-Δ (d00 pt-Δ) i H

  d11 : Δ 1 → Δ 2
  d11 x = cons-Δ x (final-Δ x) (refl-leq-Bounded-Total-Order I _)

  d12 : Δ 1 → Δ 2
  d12 x =
    cons-Δ x
      ( bottom-Bounded-Total-Order I)
      ( is-bottom-element-bottom-Bounded-Total-Order I _)

  identity-d10-d00 :
    (i : Δ 0) → d10 (d00 i) ＝ d11 (d00 i)
  identity-d10-d00 pt-Δ =
    eq-Eq-Δ (Eq-cons-Δ _ _ (refl-Eq-Δ _) refl)

  identity-d10-d01 :
    (i : Δ 0) → d10 (d01 i) ＝ d12 (d00 i)
  identity-d10-d01 pt-Δ =
    eq-Eq-Δ (Eq-cons-Δ _ _ (refl-Eq-Δ _) refl)

  identity-d11-d01 :
    (i : Δ 0) → d11 (d01 i) ＝ d12 (d01 i)
  identity-d11-d01 pt-Δ =
    eq-Eq-Δ (Eq-cons-Δ _ _ (refl-Eq-Δ _) refl)

  s00 : Δ 1 → Δ 0
  s00 i = pt-Δ

  s10 : Δ 2 → Δ 1
  s10 (cons-Δ x i H) = in-Δ i

  s11 : Δ 2 → Δ 1
  s11 x = initial-Δ _ x

  identity-s00-s10 :
    (x : Δ 2) → s00 (s10 x) ＝ s00 (s11 x)
  identity-s00-s10 (cons-Δ x i H) = refl

  module _
    {l : Level} (A : UU l)
    where
    
    nerve-Δ : ℕ → UU (l1 ⊔ l)
    nerve-Δ n = Δ n → A

    obj-Δ : UU (l1 ⊔ l)
    obj-Δ = nerve-Δ 0

    mor-Δ : UU (l1 ⊔ l)
    mor-Δ = nerve-Δ 1

  module _
    {l : Level} {A : UU l}
    where

    dom-Δ : mor-Δ A → obj-Δ A
    dom-Δ f = f ∘ d01

    cod-Δ : mor-Δ A → obj-Δ A
    cod-Δ f = f ∘ d00

    id-mor-Δ : obj-Δ A → mor-Δ A
    id-mor-Δ f = f ∘ s00

  module _
    {l2 : Level} {A : UU l2}
    where

    record
      hom-Δ (x y : obj-Δ A) : UU (l1 ⊔ l2)
      where

      field
        mor-hom-Δ : mor-Δ A
        htpy-dom-hom-Δ : dom-Δ mor-hom-Δ ~ x
        htpy-cod-hom-Δ : cod-Δ mor-hom-Δ ~ y

    open hom-Δ public

    record
      htpy-hom-Δ {x y : obj-Δ A} (f g : hom-Δ x y) : UU (l1 ⊔ l2)
      where

      field
        htpy-mor-hom-Δ : mor-hom-Δ f ~ mor-hom-Δ g
        htpy-htpy-dom-hom-Δ :
          coherence-triangle-homotopies
            ( htpy-dom-hom-Δ f)
            ( htpy-dom-hom-Δ g)
            ( htpy-mor-hom-Δ ·r d01)
        htpy-htpy-cod-hom-Δ :
          coherence-triangle-homotopies
            ( htpy-cod-hom-Δ f)
            ( htpy-cod-hom-Δ g)
            ( htpy-mor-hom-Δ ·r d00)

    open htpy-hom-Δ public

    refl-htpy-hom-Δ : {x y : obj-Δ A} (f : hom-Δ x y) → htpy-hom-Δ f f
    htpy-mor-hom-Δ (refl-htpy-hom-Δ f) = refl-htpy
    htpy-htpy-dom-hom-Δ (refl-htpy-hom-Δ f) = refl-htpy
    htpy-htpy-cod-hom-Δ (refl-htpy-hom-Δ f) = refl-htpy      

    id-Δ : (x : obj-Δ A) → hom-Δ x x
    mor-hom-Δ (id-Δ x) = x ∘ s00
    htpy-dom-hom-Δ (id-Δ x) pt-Δ = refl
    htpy-cod-hom-Δ (id-Δ x) pt-Δ = refl

  record
    midhorn {l : Level} (A : UU l) : UU (l1 ⊔ l)
    where

    constructor
      tim

    field
      fstmor sndmor : mor-Δ A
      compat : cod-Δ fstmor pt-Δ ＝ dom-Δ sndmor pt-Δ

  open midhorn public

  representing-midhorn : UU l1
  representing-midhorn =
    pushout d00 d01

  inl-representing-midhorn : Δ 1 → representing-midhorn
  inl-representing-midhorn = inl-pushout d00 d01

  inr-representing-midhorn : Δ 1 → representing-midhorn
  inr-representing-midhorn = inr-pushout d00 d01

  horn-inclusion : representing-midhorn → Δ 2
  horn-inclusion =
    cogap d00 d01 (d12 , d10 , inv ∘ identity-d10-d01)

  compute-inl-horn-inclusion :
    horn-inclusion ∘ inl-representing-midhorn ~ d12
  compute-inl-horn-inclusion =
    compute-inl-cogap d00 d01 (d12 , d10 , inv ∘ identity-d10-d01)

  compute-inr-horn-inclusion :
    horn-inclusion ∘ inr-representing-midhorn ~ d10
  compute-inr-horn-inclusion =
    compute-inr-cogap d00 d01 (d12 , d10 , inv ∘ identity-d10-d01)

  is-local-horn-inclusion : {l : Level} (A : UU l) → UU (l1 ⊔ l)
  is-local-horn-inclusion = is-local horn-inclusion

  is-segal : {l : Level} (A : UU l) → UU (l1 ⊔ l)
  is-segal A =
    (h : representing-midhorn → A) → is-contr (extension horn-inclusion h)

  extension-is-segal :
    {l : Level} {A : UU l} (H : is-segal A)
    (h : representing-midhorn → A) → extension horn-inclusion h
  extension-is-segal H h = center (H h)

  2-simplex-is-segal :
    {l : Level} {A : UU l} (H : is-segal A) →
    (h : representing-midhorn → A) → Δ 2 → A
  2-simplex-is-segal H h = map-extension (extension-is-segal H h)

  htpy-2-simplex-is-segal :
    {l : Level} {A : UU l} (H : is-segal A) →
    (h : representing-midhorn → A) →
    h ~ 2-simplex-is-segal H h ∘ horn-inclusion
  htpy-2-simplex-is-segal H h =
    is-extension-map-extension (extension-is-segal H h)

  module _
    {l : Level} {A : UU l}
    where
    
    is-segal-is-local-horn-inclusion :
      is-local-horn-inclusion A → is-segal A
    is-segal-is-local-horn-inclusion =
      is-contr-extension-is-local horn-inclusion

    is-local-horn-inclusion-is-segal :
      is-segal A → is-local-horn-inclusion A
    is-local-horn-inclusion-is-segal =
      is-local-is-contr-extension horn-inclusion

  module _
    {l2 l3 : Level} {X : UU l2} (A : X → UU l3)
    where
    
    distributive-Π-is-local-horn-inclusion :
      ((x : X) → is-local-horn-inclusion (A x)) →
      is-local-horn-inclusion ((x : X) → A x)
    distributive-Π-is-local-horn-inclusion =
      distributive-Π-is-local horn-inclusion A

    distributive-Π-is-segal :
      ((x : X) → is-segal (A x)) → is-segal ((x : X) → A x)
    distributive-Π-is-segal H =
      is-segal-is-local-horn-inclusion
        ( distributive-Π-is-local-horn-inclusion
          ( λ x → is-local-horn-inclusion-is-segal (H x)))

  module _
    {l2 : Level} {A : UU l2} (H : is-segal A)
    where

    horn-composable-hom-Δ :
      {x y z : obj-Δ A} → hom-Δ y z → hom-Δ x y → representing-midhorn → A
    horn-composable-hom-Δ g f =
      cogap d00 d01
        ( mor-hom-Δ f ,
          mor-hom-Δ g ,
          ( λ u → htpy-cod-hom-Δ f u ∙ inv (htpy-dom-hom-Δ g u)))

    compute-inl-horn-composable-hom-Δ :
      {x y z : obj-Δ A} (g : hom-Δ y z) (f : hom-Δ x y) →
      horn-composable-hom-Δ g f ∘ inl-representing-midhorn ~ mor-hom-Δ f
    compute-inl-horn-composable-hom-Δ g f =
      compute-inl-cogap
        d00 d01
        ( mor-hom-Δ f ,
          mor-hom-Δ g ,
          ( λ u → htpy-cod-hom-Δ f u ∙ inv (htpy-dom-hom-Δ g u)))

    compute-inr-horn-composable-hom-Δ :
      {x y z : obj-Δ A} (g : hom-Δ y z) (f : hom-Δ x y) →
      horn-composable-hom-Δ g f ∘ inr-representing-midhorn ~ mor-hom-Δ g
    compute-inr-horn-composable-hom-Δ g f =
      compute-inr-cogap
        d00 d01
        ( mor-hom-Δ f ,
          mor-hom-Δ g ,
          ( λ u → htpy-cod-hom-Δ f u ∙ inv (htpy-dom-hom-Δ g u)))

    comp-is-segal-witness :
      {x y z : obj-Δ A} → hom-Δ y z → hom-Δ x y → Δ 2 → A
    comp-is-segal-witness g f =
      2-simplex-is-segal H (horn-composable-hom-Δ g f)

    is-extension-comp-is-segal-witness :
      {x y z : obj-Δ A} (g : hom-Δ y z) (f : hom-Δ x y) →
      is-extension horn-inclusion
        ( horn-composable-hom-Δ g f)
        ( comp-is-segal-witness g f)
    is-extension-comp-is-segal-witness g f =
      htpy-2-simplex-is-segal H (horn-composable-hom-Δ g f)
    
    comp-is-segal : {x y z : obj-Δ A} → hom-Δ y z → hom-Δ x y → hom-Δ x z
    mor-hom-Δ (comp-is-segal g f) =
      comp-is-segal-witness g f ∘ d11
    htpy-dom-hom-Δ (comp-is-segal {x} {y} {z} g f) =
      ( comp-is-segal-witness g f ·l identity-d11-d01) ∙h
      ( inv-htpy
        ( comp-is-segal-witness g f ·l
          compute-inl-horn-inclusion ·r d01)) ∙h
      ( inv-htpy
        ( is-extension-comp-is-segal-witness g f ·r
          inl-representing-midhorn ∘ d01)) ∙h
      ( compute-inl-horn-composable-hom-Δ g f ·r d01) ∙h
      ( htpy-dom-hom-Δ f)
    htpy-cod-hom-Δ (comp-is-segal g f) =
      ( comp-is-segal-witness g f ·l
        inv-htpy identity-d10-d00) ∙h
      ( inv-htpy
        ( comp-is-segal-witness g f ·l
          compute-inr-horn-inclusion ·r d00)) ∙h
      ( inv-htpy
        ( is-extension-comp-is-segal-witness g f ·r
          inr-representing-midhorn ∘ d00)) ∙h
      ( compute-inr-horn-composable-hom-Δ g f ·r d00) ∙h
      ( htpy-cod-hom-Δ g)

    comp-is-segal-witness-uniqueness :
      {x y z : obj-Δ A} (g : hom-Δ y z) (f : hom-Δ x y)
      (α : Δ 2 → A) (β : horn-composable-hom-Δ g f ~ α ∘ horn-inclusion) →
      comp-is-segal-witness g f ~ α
    comp-is-segal-witness-uniqueness g f α β =
      htpy-eq
        ( ap pr1
          ( eq-is-contr
            ( H (horn-composable-hom-Δ g f))
            { comp-is-segal-witness g f , is-extension-comp-is-segal-witness g f}
            { α , β}))

  resmid-Δ : {l : Level} {X : UU l} → nerve-Δ X 2 → midhorn X
  fstmor (resmid-Δ f) = f ∘ d12
  sndmor (resmid-Δ f) = f ∘ d10
  compat (resmid-Δ f) = ap f (inv (identity-d10-d01 pt-Δ))
```
