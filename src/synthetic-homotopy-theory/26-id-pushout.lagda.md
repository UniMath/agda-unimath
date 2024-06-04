# Formalization of the Symmetry book - 26 id pushout

```agda
module synthetic-homotopy-theory.26-id-pushout where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.precomposition-dependent-functions
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universal-property-identity-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.descent-property-pushouts
open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Section 19.1 Characterizing families of maps over pushouts

```agda
module hom-Fam-pushout
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1}
  { A : UU l2}
  { B : UU l3}
  { f : S → A}
  { g : S → B}
  ( P : descent-data-pushout (make-span-diagram f g) l4)
  ( Q : descent-data-pushout (make-span-diagram f g) l5)
  where

  private
    PA = pr1 P
    PB = pr1 (pr2 P)
    PS = pr2 (pr2 P)
    QA = pr1 Q
    QB = pr1 (pr2 Q)
    QS = pr2 (pr2 Q)
```

### Definition 19.1.1

```agda
  hom-Fam-pushout :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  hom-Fam-pushout =
    Σ ( (x : A) → (PA x) → (QA x)) (λ hA →
      Σ ( (y : B) → (PB y) → (QB y)) (λ hB →
        ( s : S) →
          ( (hB (g s)) ∘ (map-equiv (PS s))) ~
          ( (map-equiv (QS s)) ∘ (hA (f s)))))
```

### Remark 19.1.2 We characterize the identity type of `hom-Fam-pushout`

```agda
  htpy-hom-Fam-pushout :
    ( h k : hom-Fam-pushout) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  htpy-hom-Fam-pushout h k =
    Σ ( (x : A) → (pr1 h x) ~ (pr1 k x)) (λ HA →
      Σ ( (y : B) → (pr1 (pr2 h) y) ~ (pr1 (pr2 k) y)) (λ HB →
        ( s : S) →
        ( ((HB (g s)) ·r (map-equiv (PS s))) ∙h (pr2 (pr2 k) s)) ~
        ( (pr2 (pr2 h) s) ∙h ((map-equiv (QS s)) ·l (HA (f s))))))

  reflexive-htpy-hom-Fam-pushout :
    ( h : hom-Fam-pushout) → htpy-hom-Fam-pushout h h
  reflexive-htpy-hom-Fam-pushout h =
    pair
      ( λ x → refl-htpy)
      ( pair
        ( λ y → refl-htpy)
        ( λ s → inv-htpy-right-unit-htpy))

  htpy-hom-Fam-pushout-eq :
    ( h k : hom-Fam-pushout) → Id h k → htpy-hom-Fam-pushout h k
  htpy-hom-Fam-pushout-eq h .h refl =
    reflexive-htpy-hom-Fam-pushout h

  is-torsorial-htpy-hom-Fam-pushout :
    ( h : hom-Fam-pushout) → is-torsorial (htpy-hom-Fam-pushout h)
  is-torsorial-htpy-hom-Fam-pushout h =
    is-torsorial-Eq-structure
      ( is-torsorial-Eq-Π
        ( λ x → is-torsorial-htpy (pr1 h x)))
      ( pair (pr1 h) (λ x → refl-htpy))
      ( is-torsorial-Eq-structure
        ( is-torsorial-Eq-Π
          ( λ y → is-torsorial-htpy (pr1 (pr2 h) y)))
        ( pair (pr1 (pr2 h)) (λ y → refl-htpy))
        ( is-torsorial-Eq-Π
          ( λ s → is-torsorial-htpy'
            ((pr2 (pr2 h) s) ∙h ((map-equiv (QS s)) ·l refl-htpy)))))

  is-equiv-htpy-hom-Fam-pushout-eq :
    ( h k : hom-Fam-pushout) → is-equiv (htpy-hom-Fam-pushout-eq h k)
  is-equiv-htpy-hom-Fam-pushout-eq h =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-Fam-pushout h)
      ( htpy-hom-Fam-pushout-eq h)

  eq-htpy-hom-Fam-pushout :
    ( h k : hom-Fam-pushout) → htpy-hom-Fam-pushout h k → Id h k
  eq-htpy-hom-Fam-pushout h k =
    map-inv-is-equiv (is-equiv-htpy-hom-Fam-pushout-eq h k)

open hom-Fam-pushout public
```

### Definition 19.1.3

Given a cocone structure on `X` and a family of maps indexed by `X`, we obtain a
morphism of descent data.

```agda
Naturality-fam-maps :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( f : (a : A) → B a → C a) {x x' : A} (p : Id x x') → UU (l2 ⊔ l3)
Naturality-fam-maps {B = B} {C} f {x} {x'} p =
  (y : B x) → Id (f x' (tr B p y)) (tr C p (f x y))

naturality-fam-maps :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( f : (a : A) → B a → C a) {x x' : A} (p : Id x x') →
  Naturality-fam-maps f p
naturality-fam-maps f refl y = refl

hom-Fam-pushout-map :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( P : X → UU l5) (Q : X → UU l6) → ((x : X) → P x → Q x) →
  hom-Fam-pushout
    ( descent-data-family-cocone-span-diagram c P)
    ( descent-data-family-cocone-span-diagram c Q)
hom-Fam-pushout-map {f = f} {g} c P Q h =
  pair
    ( precomp-Π (pr1 c) (λ x → P x → Q x) h)
    ( pair
      ( precomp-Π (pr1 (pr2 c)) (λ x → P x → Q x) h)
      ( λ s → naturality-fam-maps h (pr2 (pr2 c) s)))
```

### Theorem 19.1.4 The function `hom-Fam-pushout-map` is an equivalence

```agda
square-path-over-fam-maps :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  { x x' : A} (p : Id x x') (f : B x → C x) (f' : B x' → C x') →
  Id (tr (λ a → B a → C a) p f) f' →
  ( y : B x) → Id (f' (tr B p y)) (tr C p (f y))
square-path-over-fam-maps refl f f' = htpy-eq ∘ inv

hom-Fam-pushout-dependent-cocone :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( P : X → UU l5) (Q : X → UU l6) →
  dependent-cocone f g c (λ x → P x → Q x) →
  hom-Fam-pushout
    ( descent-data-family-cocone-span-diagram c P)
    ( descent-data-family-cocone-span-diagram c Q)
hom-Fam-pushout-dependent-cocone {f = f} {g} c P Q =
  tot (λ hA → tot (λ hB →
    map-Π (λ s →
      square-path-over-fam-maps (pr2 (pr2 c) s) (hA (f s)) (hB (g s)))))

is-equiv-square-path-over-fam-maps :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  { x x' : A} (p : Id x x') (f : B x → C x) (f' : B x' → C x') →
  is-equiv (square-path-over-fam-maps p f f')
is-equiv-square-path-over-fam-maps refl f f' =
  is-equiv-comp htpy-eq inv (is-equiv-inv f f') (funext f' f)

is-equiv-hom-Fam-pushout-dependent-cocone :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( P : X → UU l5) (Q : X → UU l6) →
  is-equiv (hom-Fam-pushout-dependent-cocone c P Q)
is-equiv-hom-Fam-pushout-dependent-cocone {f = f} {g} c P Q =
  is-equiv-tot-is-fiberwise-equiv (λ hA →
    is-equiv-tot-is-fiberwise-equiv (λ hB →
      is-equiv-map-Π-is-fiberwise-equiv
        ( λ s → is-equiv-square-path-over-fam-maps
          ( pr2 (pr2 c) s)
          ( hA (f s))
          ( hB (g s)))))

coherence-naturality-fam-maps :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (P : B → UU l3) (Q : B → UU l4) →
  { f f' : A → B} (H : f ~ f') (h : (b : B) → P b → Q b) (a : A) →
  Id
    ( square-path-over-fam-maps (H a) (h (f a)) (h (f' a)) (apd h (H a)))
    ( naturality-fam-maps h (H a))
coherence-naturality-fam-maps {A = A} {B} P Q {f} {f'} H =
  ind-htpy f
    ( λ f' H →
      ( h : (b : B) → P b → Q b) (a : A) →
      Id
        ( square-path-over-fam-maps (H a) (h (f a)) (h (f' a)) (apd h (H a)))
        ( naturality-fam-maps h (H a)))
    ( λ h a → refl)
    ( H)

triangle-hom-Fam-pushout-dependent-cocone :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( P : X → UU l5) (Q : X → UU l6) →
  ( hom-Fam-pushout-map c P Q) ~
  ( ( hom-Fam-pushout-dependent-cocone c P Q) ∘
    ( dependent-cocone-map f g c (λ x → P x → Q x)))
triangle-hom-Fam-pushout-dependent-cocone {f = f} {g} c P Q h =
  eq-htpy-hom-Fam-pushout
    ( descent-data-family-cocone-span-diagram c P)
    ( descent-data-family-cocone-span-diagram c Q)
    ( hom-Fam-pushout-map c P Q h)
    ( hom-Fam-pushout-dependent-cocone c P Q
      ( dependent-cocone-map f g c (λ x → P x → Q x) h))
    ( pair
      ( λ a → refl-htpy)
      ( pair
        ( λ b → refl-htpy)
        ( λ s →
          ( htpy-eq
            ( coherence-naturality-fam-maps P Q (pr2 (pr2 c)) h s)) ∙h
          ( inv-htpy-right-unit-htpy))))

is-equiv-hom-Fam-pushout-map :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : universal-property-pushout f g c)
  ( P : X → UU l5) (Q : X → UU l6) →
  is-equiv (hom-Fam-pushout-map c P Q)
is-equiv-hom-Fam-pushout-map {l5 = l5} {l6} {f = f} {g} c up-X P Q =
  is-equiv-left-map-triangle
    ( hom-Fam-pushout-map c P Q)
    ( hom-Fam-pushout-dependent-cocone c P Q)
    ( dependent-cocone-map f g c (λ x → P x → Q x))
    ( triangle-hom-Fam-pushout-dependent-cocone c P Q)
    ( dependent-universal-property-universal-property-pushout
      f g c up-X (λ x → P x → Q x))
    ( is-equiv-hom-Fam-pushout-dependent-cocone c P Q)

equiv-hom-Fam-pushout-map :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : universal-property-pushout f g c)
  ( P : X → UU l5) (Q : X → UU l6) →
  ( (x : X) → P x → Q x) ≃
  hom-Fam-pushout
    ( descent-data-family-cocone-span-diagram c P)
    ( descent-data-family-cocone-span-diagram c Q)
equiv-hom-Fam-pushout-map c up-X P Q =
  pair
    ( hom-Fam-pushout-map c P Q)
    ( is-equiv-hom-Fam-pushout-map c up-X P Q)
```

### Definition 19.2.1 Universal families over spans

```agda
ev-point-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B}
  ( P : descent-data-pushout (make-span-diagram f g) l4)
  ( Q : descent-data-pushout (make-span-diagram f g) l5)
  {a : A} → (pr1 P a) → (hom-Fam-pushout P Q) → pr1 Q a
ev-point-hom-Fam-pushout P Q {a} p h = pr1 h a p

is-universal-Fam-pushout :
  { l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B}
  ( P : descent-data-pushout (make-span-diagram f g) l4) (a : A) (p : pr1 P a) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
is-universal-Fam-pushout l {f = f} {g} P a p =
  ( Q : descent-data-pushout (make-span-diagram f g) l) →
  is-equiv (ev-point-hom-Fam-pushout P Q p)
```

### Lemma 19.2.2 The descent data of the identity type is a universal family

```agda
triangle-is-universal-id-Fam-pushout' :
  { l l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X)
  (a : A) ( Q : (x : X) → UU l) →
  ( ev-refl (pr1 c a) {B = λ x p → Q x}) ~
  ( ( ev-point-hom-Fam-pushout
      ( descent-data-family-cocone-span-diagram c (Id (pr1 c a)))
      ( descent-data-family-cocone-span-diagram c Q)
      ( refl)) ∘
    ( hom-Fam-pushout-map c (Id (pr1 c a)) Q))
triangle-is-universal-id-Fam-pushout' c a Q = refl-htpy

is-universal-id-Fam-pushout' :
  { l l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X)
  ( up-X : universal-property-pushout f g c) (a : A) →
  ( Q : (x : X) → UU l) →
  is-equiv
    ( ev-point-hom-Fam-pushout
      ( descent-data-family-cocone-span-diagram c (Id (pr1 c a)))
      ( descent-data-family-cocone-span-diagram c Q)
      ( refl))
is-universal-id-Fam-pushout' c up-X a Q =
  is-equiv-right-map-triangle
    ( ev-refl (pr1 c a) {B = λ x p → Q x})
    ( ev-point-hom-Fam-pushout
      ( descent-data-family-cocone-span-diagram c (Id (pr1 c a)))
      ( descent-data-family-cocone-span-diagram c Q)
      ( refl))
    ( hom-Fam-pushout-map c (Id (pr1 c a)) Q)
    ( triangle-is-universal-id-Fam-pushout' c a Q)
    ( is-equiv-ev-refl (pr1 c a))
    ( is-equiv-hom-Fam-pushout-map c up-X (Id (pr1 c a)) Q)

is-universal-id-Fam-pushout :
  { l1 l2 l3 l4 l : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X)
  ( up-X : universal-property-pushout f g c) (a : A) →
  is-universal-Fam-pushout l
    ( descent-data-family-cocone-span-diagram c (Id (pr1 c a)))
    ( a)
    ( refl)
is-universal-id-Fam-pushout {S = S} {A} {B} {X} {f} {g} c up-X a Q =
  map-inv-is-equiv
    ( is-equiv-precomp-Π-is-equiv
      ( is-equiv-descent-data-family-cocone-span-diagram up-X)
      ( λ (Q : descent-data-pushout (make-span-diagram f g) _) →
        is-equiv
          ( ev-point-hom-Fam-pushout
            ( descent-data-family-cocone-span-diagram c (Id (pr1 c a)))
            ( Q)
            ( refl))))
    ( is-universal-id-Fam-pushout' c up-X a)
    ( Q)
```

We construct the identity morphism and composition, and we show that morphisms
equipped with two-sided inverses are equivalences.

```agda
id-hom-Fam-pushout :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : descent-data-pushout (make-span-diagram f g) l4) → hom-Fam-pushout P P
id-hom-Fam-pushout P =
  pair
    ( λ a → id)
    ( pair
      ( λ b → id)
      ( λ s → refl-htpy))

comp-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : descent-data-pushout (make-span-diagram f g) l4)
  ( Q : descent-data-pushout (make-span-diagram f g) l5)
  ( R : descent-data-pushout (make-span-diagram f g) l6) →
  hom-Fam-pushout Q R → hom-Fam-pushout P Q → hom-Fam-pushout P R
comp-hom-Fam-pushout {f = f} {g} P Q R k h =
  pair
    ( λ a → (pr1 k a) ∘ (pr1 h a))
    ( pair
      ( λ b → (pr1 (pr2 k) b) ∘ (pr1 (pr2 h) b))
      ( λ s →
        pasting-horizontal-coherence-square-maps
          ( pr1 h (f s))
          ( pr1 k (f s))
          ( map-equiv (pr2 (pr2 P) s))
          ( map-equiv (pr2 (pr2 Q) s))
          ( map-equiv (pr2 (pr2 R) s))
          ( pr1 (pr2 h) (g s))
          ( pr1 (pr2 k) (g s))
          ( pr2 (pr2 h) s)
          ( pr2 (pr2 k) s)))

is-invertible-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : descent-data-pushout (make-span-diagram f g) l4)
  ( Q : descent-data-pushout (make-span-diagram f g) l5)
  ( h : hom-Fam-pushout P Q) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
is-invertible-hom-Fam-pushout P Q h =
  Σ ( hom-Fam-pushout Q P) (λ k →
    ( htpy-hom-Fam-pushout Q Q
      ( comp-hom-Fam-pushout Q P Q h k)
      ( id-hom-Fam-pushout Q)) ×
    ( htpy-hom-Fam-pushout P P
      ( comp-hom-Fam-pushout P Q P k h)
      ( id-hom-Fam-pushout P)))

is-equiv-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B}
  ( P : descent-data-pushout (make-span-diagram f g) l4)
  ( Q : descent-data-pushout (make-span-diagram f g) l5) →
  hom-Fam-pushout P Q → UU (l2 ⊔ l3 ⊔ l4 ⊔ l5)
is-equiv-hom-Fam-pushout {A = A} {B} {f} {g} P Q h =
  ((a : A) → is-equiv (pr1 h a)) × ((b : B) → is-equiv (pr1 (pr2 h) b))

is-equiv-is-invertible-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : descent-data-pushout (make-span-diagram f g) l4)
  ( Q : descent-data-pushout (make-span-diagram f g) l5)
  (h : hom-Fam-pushout P Q) →
  is-invertible-hom-Fam-pushout P Q h → is-equiv-hom-Fam-pushout P Q h
is-equiv-is-invertible-hom-Fam-pushout P Q h has-inv-h =
  pair
    ( λ a →
      is-equiv-is-invertible
        ( pr1 (pr1 has-inv-h) a)
        ( pr1 (pr1 (pr2 has-inv-h)) a)
        ( pr1 (pr2 (pr2 has-inv-h)) a))
    ( λ b →
      is-equiv-is-invertible
        ( pr1 (pr2 (pr1 has-inv-h)) b)
        ( pr1 (pr2 (pr1 (pr2 has-inv-h))) b)
        ( pr1 (pr2 (pr2 (pr2 has-inv-h))) b))

equiv-is-equiv-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B}
  ( P : descent-data-pushout (make-span-diagram f g) l4)
  ( Q : descent-data-pushout (make-span-diagram f g) l5) →
  ( h : hom-Fam-pushout P Q) →
  is-equiv-hom-Fam-pushout P Q h → equiv-descent-data-pushout P Q
equiv-is-equiv-hom-Fam-pushout P Q h is-equiv-h =
  pair
    ( λ a → pair (pr1 h a) (pr1 is-equiv-h a))
    ( pair
      ( λ b → pair (pr1 (pr2 h) b) (pr2 is-equiv-h b))
      ( pr2 (pr2 h)))
```

### Theorem 19.1.3 Characterization of identity types of pushouts

```agda
{-
hom-identity-is-universal-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l5}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : universal-property-pushout f g c) →
  ( P : Fam-pushout l4 f g) (a : A) (p : pr1 P a) →
  is-universal-Fam-pushout l5 P a p →
  Σ ( hom-Fam-pushout P (desc-fam c (Id (pr1 c a))))
    ( λ h → Id (pr1 h a p) refl)
hom-identity-is-universal-Fam-pushout {f = f} {g} c up-X P a p is-univ-P =
  {!!}

is-identity-is-universal-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l5}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : universal-property-pushout f g c) →
  ( P : Fam-pushout l4 f g) (a : A) (p : pr1 P a) →
  is-universal-Fam-pushout l5 P a p →
  Σ ( equiv-Fam-pushout P (desc-fam c (Id (pr1 c a))))
    ( λ e → Id (map-equiv (pr1 e a) p) refl)
is-identity-is-universal-Fam-pushout {f = f} {g} c up-X a P p₀ is-eq-P = {!!}
-}
```
