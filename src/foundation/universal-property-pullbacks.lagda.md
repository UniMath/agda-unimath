# The universal property of pullbacks

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.universal-property-pullbacks where

open import foundation.cartesian-product-types using (_×_)
open import foundation.commuting-squares using (coherence-square)
open import foundation.contractible-maps using (is-contr-map-is-equiv)
open import foundation.contractible-types using (is-contr; is-contr-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2; triple)
open import foundation.equivalences using
  ( is-equiv; is-property-is-equiv; map-inv-is-equiv; issec-map-inv-is-equiv;
    _≃_; is-equiv-right-factor; is-equiv-comp; is-equiv-left-factor; map-equiv;
    id-equiv; _∘e_; map-inv-equiv; is-equiv-map-equiv)
open import foundation.function-extensionality using (equiv-funext)
open import foundation.functions using (_∘_)
open import foundation.functoriality-function-types using
  ( is-equiv-is-equiv-postcomp; is-equiv-postcomp-is-equiv)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id')
open import foundation.homotopies using
  ( _·r_; _~_; _∙h_; htpy-left-whisk; refl-htpy; right-unit-htpy;
    is-contr-total-htpy; equiv-concat-htpy)
open import foundation.identity-types using (Id; inv; ap; refl)
open import foundation.propositions using (is-prop; is-prop-Π)
open import foundation.structure-identity-principle using
  ( extensionality-Σ)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

The universal property of pullbacks describes the optimal way to complete a diagram of the form

```md
           B
           |
           |
           V
  A -----> X
```

to a square

```md
  C -----> B
  |        |
  |        |
  V        V
  A -----> X
```

## Definitions

### Cospans

A cospan is a pair of functions with a common codomain

```agda
cospan :
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2) →
  UU (l1 ⊔ (l2 ⊔ (lsuc l)))
cospan l A B =
  Σ (UU l) (λ X → (A → X) × (B → X))
```

### Cones on cospans

A cone on a cospan with a vertex C is a pair of functions from C into the domains of the maps in the cospan, equipped with a homotopy witnessing that the resulting square commutes.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where
   
  cone : {l4 : Level} → UU l4 → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
  cone C = Σ (C → A) (λ p → Σ (C → B) (λ q → coherence-square q p g f))

  {- A map into the vertex of a cone induces a new cone. -}
  
  cone-map :
    {l4 l5 : Level} {C : UU l4} {C' : UU l5} → cone C → (C' → C) → cone C'
  pr1 (cone-map c h) = (pr1 c) ∘ h
  pr1 (pr2 (cone-map c h)) = pr1 (pr2 c) ∘ h
  pr2 (pr2 (cone-map c h)) = pr2 (pr2 c) ·r h
```

### The universal property of pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} (l : Level) {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C)
  where
  
  universal-property-pullback : UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l4 ⊔ (lsuc l)))))
  universal-property-pullback =
    (C' : UU l) → is-equiv (cone-map f g {C' = C'} c)
```

## Properties

### The universal property is a property

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C)
  where

  abstract
    is-prop-universal-property-pullback :
      is-prop (universal-property-pullback l5 f g c)
    is-prop-universal-property-pullback =
      is-prop-Π (λ C' → is-property-is-equiv (cone-map f g c))

  map-universal-property-pullback :
    ({l : Level} → universal-property-pullback l f g c) →
    {C' : UU l5} (c' : cone f g C') → C' → C
  map-universal-property-pullback up-c {C'} c' =
    map-inv-is-equiv (up-c C') c'

  eq-map-universal-property-pullback :
    (up-c : {l : Level} → universal-property-pullback l f g c) →
    {C' : UU l5} (c' : cone f g C') →
    Id (cone-map f g c (map-universal-property-pullback up-c c')) c'
  eq-map-universal-property-pullback up-c {C'} c' =
    issec-map-inv-is-equiv (up-c C') c'
```

### Identifications of cones

Next we characterize the identity type of the type of cones with a given vertex C. Note that in the definition of htpy-cone we do not use pattern matching on the cones c and c'. This is to ensure that the type htpy-cone f g c c' is a Σ-type for any c and c', not just for c and c' of the form (pair p (pair q H)) and (pair p' (pair q' H')) respectively.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4}
  where
  
  coherence-htpy-cone :
    (c c' : cone f g C) (K : (pr1 c) ~ (pr1 c'))
    (L : (pr1 (pr2 c)) ~ (pr1 (pr2 c'))) → UU (l4 ⊔ l3)
  coherence-htpy-cone c c' K L =
    ( (pr2 (pr2 c)) ∙h (htpy-left-whisk g L)) ~
    ( (htpy-left-whisk f K) ∙h (pr2 (pr2 c')))

  htpy-cone : cone f g C → cone f g C → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
  htpy-cone c c' =
    Σ ( (pr1 c) ~ (pr1 c'))
      ( λ K → Σ ((pr1 (pr2 c)) ~ (pr1 (pr2 c')))
        ( λ L → coherence-htpy-cone c c' K L))

  refl-htpy-cone : (c : cone f g C) → htpy-cone c c
  pr1 (refl-htpy-cone c) = refl-htpy
  pr1 (pr2 (refl-htpy-cone c)) = refl-htpy
  pr2 (pr2 (refl-htpy-cone c)) = right-unit-htpy
      
  htpy-eq-cone : (c c' : cone f g C) → Id c c' → htpy-cone c c'
  htpy-eq-cone c .c refl = refl-htpy-cone c

  extensionality-cone : (c d : cone f g C) → Id c d ≃ htpy-cone c d
  extensionality-cone (pair p (pair q H)) =
    extensionality-Σ
      ( λ {p'} qH' K →
        Σ ( q ~ pr1 qH')
            ( coherence-htpy-cone (pair p (pair q H)) (pair p' qH') K))
      ( refl-htpy)
      ( pair refl-htpy right-unit-htpy)
      ( λ p' → equiv-funext)
      ( extensionality-Σ
        ( λ {q'} H' →
          coherence-htpy-cone
            ( pair p (pair q H))
            ( pair p (pair q' H'))
            ( refl-htpy))
        ( refl-htpy)
        ( right-unit-htpy)
        ( λ q' → equiv-funext)
        ( λ H' → equiv-concat-htpy right-unit-htpy H' ∘e equiv-funext))

  is-contr-total-htpy-cone :
    (c : cone f g C) → is-contr (Σ (cone f g C) (htpy-cone c))
  is-contr-total-htpy-cone c =
     fundamental-theorem-id' c
       ( refl-htpy-cone c)
       ( λ c' → map-equiv (extensionality-cone c c'))
       ( λ c' → is-equiv-map-equiv (extensionality-cone c c'))

  eq-htpy-cone :
    (c c' : cone f g C) → htpy-cone c c' → Id c c'
  eq-htpy-cone c c' = map-inv-equiv (extensionality-cone c c')
```

### The homotopy of cones obtained from the universal property of pullbacks

```
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4}
  where
  
  htpy-cone-map-universal-property-pullback :
    (c : cone f g C) (up : {l : Level} → universal-property-pullback l f g c) →
    {l5 : Level} {C' : UU l5} (c' : cone f g C') →
    htpy-cone f g
      ( cone-map f g c (map-universal-property-pullback f g c up c'))
      ( c')
  htpy-cone-map-universal-property-pullback c up c' =
    htpy-eq-cone f g
      ( cone-map f g c (map-universal-property-pullback f g c up c'))
      ( c')
      ( eq-map-universal-property-pullback f g c up c')
```

### Uniqueness of maps obtained via the universal property of pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C)
  where

  abstract
    uniqueness-universal-property-pullback :
      ({l : Level} → universal-property-pullback l f g c) →
      {l5 : Level} (C' : UU l5) (c' : cone f g C') →
      is-contr (Σ (C' → C) (λ h → htpy-cone f g (cone-map f g c h) c'))
    uniqueness-universal-property-pullback up C' c' =
      is-contr-equiv'
        ( Σ (C' → C) (λ h → Id (cone-map f g c h) c'))
        ( equiv-tot
          ( λ h → extensionality-cone f g (cone-map f g c h) c'))
        ( is-contr-map-is-equiv (up C')  c')
```

### 3-for-2 property of pullbacks

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4} {C' : UU l5}
  {f : A → X} {g : B → X} (c : cone f g C) (c' : cone f g C')
  (h : C' → C) (KLM : htpy-cone f g (cone-map f g c h) c')
  where
  
  triangle-cone-cone :
    {l6 : Level} (D : UU l6) →
    (cone-map f g {C' = D} c') ~ ((cone-map f g c) ∘ (λ (k : D → C') → h ∘ k))
  triangle-cone-cone D k = 
    inv
      ( ap
        ( λ t → cone-map f g {C' = D} t k)
        { x = (cone-map f g c h)}
        { y = c'}
        ( eq-htpy-cone f g (cone-map f g c h) c' KLM))

  abstract
    is-equiv-up-pullback-up-pullback :
      ({l : Level} → universal-property-pullback l f g c) →
      ({l : Level} → universal-property-pullback l f g c') →
      is-equiv h
    is-equiv-up-pullback-up-pullback up up' =
      is-equiv-is-equiv-postcomp h
        ( λ D → is-equiv-right-factor
          ( cone-map f g {C' = D} c')
          ( cone-map f g c)
          ( λ (k : D → C') → h ∘ k)
          ( triangle-cone-cone D)
          ( up D)
          ( up' D))

  abstract
    up-pullback-up-pullback-is-equiv :
      is-equiv h →
      ({l : Level} → universal-property-pullback l f g c) →
      ({l : Level} → universal-property-pullback l f g c')
    up-pullback-up-pullback-is-equiv is-equiv-h up D =
      is-equiv-comp
        ( cone-map f g c')
        ( cone-map f g c)
        ( λ k → h ∘ k)
        ( triangle-cone-cone D)
        ( is-equiv-postcomp-is-equiv h is-equiv-h D)
        ( up D)

  abstract
    up-pullback-is-equiv-up-pullback :
      ({l : Level} → universal-property-pullback l f g c') →
      is-equiv h →
      ({l : Level} → universal-property-pullback l f g c)
    up-pullback-is-equiv-up-pullback up' is-equiv-h D =
      is-equiv-left-factor
        ( cone-map f g c')
        ( cone-map f g c)
        ( λ k → h ∘ k)
        ( triangle-cone-cone D)
        ( up' D)
        ( is-equiv-postcomp-is-equiv h is-equiv-h D)
```

### Uniquely uniqueness of pullbacks

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} {C' : UU l5}
  where

  abstract
    uniquely-unique-pullback :
      ( c' : cone f g C') (c : cone f g C) →
      ( up-c' : {l : Level} → universal-property-pullback l f g c') →
      ( up-c : {l : Level} → universal-property-pullback l f g c) →
      is-contr
        ( Σ (C' ≃ C) (λ e → htpy-cone f g (cone-map f g c (map-equiv e)) c'))
    uniquely-unique-pullback c' c up-c' up-c =
      is-contr-total-Eq-subtype
        ( uniqueness-universal-property-pullback f g c up-c C' c')
        ( is-property-is-equiv)
        ( map-universal-property-pullback f g c up-c c')
        ( htpy-cone-map-universal-property-pullback f g c up-c c')
        ( is-equiv-up-pullback-up-pullback c c'
          ( map-universal-property-pullback f g c up-c c')
          ( htpy-cone-map-universal-property-pullback f g c up-c c')
          up-c up-c')
```
