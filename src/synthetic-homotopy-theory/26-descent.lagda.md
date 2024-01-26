# Formalization of the Symmetry book - 26 descent

```agda
module synthetic-homotopy-theory.26-descent where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.cones-over-cospan-diagrams
open import foundation.constant-type-families
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.precomposition-functions
open import foundation.pullbacks
open import foundation.retractions
open import foundation.sections
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-pullback-property-pushouts
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.operations-cocones-under-span-diagrams
open import synthetic-homotopy-theory.pullback-property-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

### Remark 18.1.3 Computation of the identity type of `dependent-cocone`

Before we state the main theorem of this section, we also state a dependent
version of the pullback property of pushouts.

## Theorem 18.1.4

    The following properties are all equivalent:

    1. universal-property-pushout
    2. pullback-property-pushout
    3. dependent-pullback-property-pushout
    4. dependent-universal-property-pushout
    5. Ind-pushout

We have already shown (1) ↔ (2). Therefore we will first show (3) ↔ (4) ↔ (5).
Finally, we will show (2) ↔ (3). Here are the precise references to the proofs
of those parts:

- Proof of (1) → (2): `pullback-property-pushout-universal-property-pushout`
- Proof of (2) → (1): `universal-property-pushout-pullback-property-pushout`
- Proof of (2) → (3): `dependent-pullback-property-pullback-property-pushout`
- Proof of (3) → (2): `pullback-property-dependent-pullback-property-pushout`
- Proof of (3) → (4):
  `dependent-universal-property-dependent-pullback-property-pushout`
- Proof of (4) → (3):
  `dependent-pullback-property-dependent-universal-property-pushout`
- Proof of (4) → (5): `Ind-pushout-dependent-universal-property-pushout`
- Proof of (5) → (4): `dependent-universal-property-pushout-Ind-pushout`

### Proof of Theorem 18.1.4, (3) implies (2)

```agda
pullback-property-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X) →
  dependent-pullback-property-pushout 𝒮 c →
  pullback-property-pushout 𝒮 c
pullback-property-dependent-pullback-property-pushout
  l 𝒮 c dpb Y =
  is-pullback-htpy
    ( λ h →
      eq-htpy
        ( λ s →
          inv
            ( tr-constant-type-family
              ( coherence-square-cocone-span-diagram 𝒮 c s)
              ( h (left-map-span-diagram 𝒮 s)))))
    ( refl-htpy)
    { c =
      pair
        ( _∘ left-map-cocone-span-diagram 𝒮 c)
        ( pair
          ( _∘ right-map-cocone-span-diagram 𝒮 c)
          ( λ h → eq-htpy (h ·l coherence-square-cocone-span-diagram 𝒮 c)))}
    ( cone-dependent-pullback-property-pushout 𝒮 c (λ x → Y))
    ( pair
      ( λ h → refl)
      ( pair
        ( λ h → refl)
        ( λ h →
          ( right-unit) ∙
          ( ( ap
              ( eq-htpy)
              ( eq-htpy
                ( λ s →
                  left-transpose-eq-concat
                    ( tr-constant-type-family
                      ( coherence-square-cocone-span-diagram 𝒮 c s)
                      ( h
                        ( left-map-cocone-span-diagram 𝒮 c
                          ( left-map-span-diagram 𝒮 s))))
                    ( ap h (coherence-square-cocone-span-diagram 𝒮 c s))
                    ( apd h (coherence-square-cocone-span-diagram 𝒮 c s))
                    ( inv
                      ( apd-constant-type-family h
                        ( coherence-square-cocone-span-diagram 𝒮 c s)))))) ∙
            ( eq-htpy-concat-htpy
              ( λ s →
                inv
                  ( tr-constant-type-family
                    ( coherence-square-cocone-span-diagram 𝒮 c s)
                    ( h
                      ( left-map-cocone-span-diagram 𝒮 c
                        ( left-map-span-diagram 𝒮 s)))))
              ( λ s →
                apd h (coherence-square-cocone-span-diagram 𝒮 c s)))))))
    ( dpb (λ x → Y))
```

### Proof of Theorem 18.1.4, (2) implies (3)

We first define the family of lifts, which is indexed by maps $Y → X$.

```agda
fam-lifts :
  {l1 l2 l3 : Level} (Y : UU l1) {X : UU l2} (P : X → UU l3) →
  (Y → X) → UU (l1 ⊔ l3)
fam-lifts Y P h = (y : Y) → P (h y)

tr-fam-lifts' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
  (h : B → X) {f g : A → B} (H : f ~ g) →
  fam-lifts A P (h ∘ f) → fam-lifts A P (h ∘ g)
tr-fam-lifts' P h {f} {g} H k s = tr (P ∘ h) (H s) (k s)

TR-EQ-HTPY-FAM-LIFTS :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
  (h : B → X) {f g : A → B} (H : f ~ g) → UU (l1 ⊔ l4)
TR-EQ-HTPY-FAM-LIFTS {A = A} P h H =
  tr (fam-lifts A P) (eq-htpy (h ·l H)) ~ (tr-fam-lifts' P h H)

tr-eq-htpy-fam-lifts-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
  (h : B → X) (f : A → B) → TR-EQ-HTPY-FAM-LIFTS P h (refl-htpy' f)
tr-eq-htpy-fam-lifts-refl-htpy P h f k =
  ap (λ t → tr (fam-lifts _ P) t k) (eq-htpy-refl-htpy (h ∘ f))

abstract
  tr-eq-htpy-fam-lifts :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
    (h : B → X) {f g : A → B} (H : f ~ g) →
    TR-EQ-HTPY-FAM-LIFTS P h H
  tr-eq-htpy-fam-lifts P h {f} =
    ind-htpy f
      ( λ g H → TR-EQ-HTPY-FAM-LIFTS P h H)
      ( tr-eq-htpy-fam-lifts-refl-htpy P h f)

  compute-tr-eq-htpy-fam-lifts :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
    (h : B → X) (f : A → B) →
    Id ( tr-eq-htpy-fam-lifts P h (refl-htpy' f))
        ( tr-eq-htpy-fam-lifts-refl-htpy P h f)
  compute-tr-eq-htpy-fam-lifts P h f =
    compute-ind-htpy f
      ( λ g H → TR-EQ-HTPY-FAM-LIFTS P h H)
      ( tr-eq-htpy-fam-lifts-refl-htpy P h f)
```

One of the basic operations on lifts is precomposition by an ordinary function.

```agda
precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) → (f : A → B) → (h : B → X) →
  (fam-lifts B P h) → (fam-lifts A P (h ∘ f))
precompose-lifts P f h h' a = h' (f a)
```

Given two homotopic maps, their precomposition functions have different
codomains. However, there is a commuting triangle. We obtain this triangle by
homotopy induction.

```agda
TRIANGLE-PRECOMPOSE-LIFTS :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  ( P : X → UU l4) {f g : A → B} (H : f ~ g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
TRIANGLE-PRECOMPOSE-LIFTS {A = A} {B} {X} P {f} {g} H =
  (h : B → X) →
    ( (tr (fam-lifts A P) (eq-htpy (h ·l H))) ∘ (precompose-lifts P f h)) ~
    ( precompose-lifts P g h)

triangle-precompose-lifts-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) → TRIANGLE-PRECOMPOSE-LIFTS P (refl-htpy' f)
triangle-precompose-lifts-refl-htpy {A = A} P f h h' =
  tr-eq-htpy-fam-lifts-refl-htpy P h f (λ a → h' (f a))

triangle-precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) {f g : A → B} (H : f ~ g) →
  TRIANGLE-PRECOMPOSE-LIFTS P H
triangle-precompose-lifts {A = A} P {f} =
  ind-htpy f
    ( λ g H → TRIANGLE-PRECOMPOSE-LIFTS P H)
    ( triangle-precompose-lifts-refl-htpy P f)

compute-triangle-precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) →
  Id
    ( triangle-precompose-lifts P (refl-htpy' f))
    ( triangle-precompose-lifts-refl-htpy P f)
compute-triangle-precompose-lifts P f =
  compute-ind-htpy f
    ( λ g → TRIANGLE-PRECOMPOSE-LIFTS P)
    ( triangle-precompose-lifts-refl-htpy P f)
```

There is a similar commuting triangle with the computed transport function. This
time we don't use homotopy induction to construct the homotopy. We give an
explicit definition instead.

```agda
triangle-precompose-lifts' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) {f g : A → B} (H : f ~ g) → (h : B → X) →
  ( (tr-fam-lifts' P h H) ∘ (precompose-lifts P f h)) ~
  ( precompose-lifts P g h)
triangle-precompose-lifts' P H h k = eq-htpy (λ a → apd k (H a))

compute-triangle-precompose-lifts' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) → (h : B → X) →
  ( triangle-precompose-lifts' P (refl-htpy' f) h) ~
  ( refl-htpy' ( precompose-lifts P f h))
compute-triangle-precompose-lifts' P f h k = eq-htpy-refl-htpy _
```

There is a coherence between the two commuting triangles. This coherence is
again constructed by homotopy induction.

```agda
COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  {f g : A → B} (H : f ~ g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS {A = A} {B} {X} P {f} {g} H =
  (h : B → X) →
    ( triangle-precompose-lifts P H h) ~
    ( ( ( tr-eq-htpy-fam-lifts P h H) ·r (precompose-lifts P f h)) ∙h
      ( triangle-precompose-lifts' P H h))

coherence-triangle-precompose-lifts-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  (f : A → B) → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P (refl-htpy' f)
coherence-triangle-precompose-lifts-refl-htpy P f h =
  ( htpy-eq (htpy-eq (compute-triangle-precompose-lifts P f) h)) ∙h
  ( ( ( inv-htpy-right-unit-htpy) ∙h
      ( ap-concat-htpy
        ( λ h' → tr-eq-htpy-fam-lifts-refl-htpy P h f (λ a → h' (f a)))
        ( inv-htpy (compute-triangle-precompose-lifts' P f h)))) ∙h
    ( htpy-eq
      ( ap
        ( λ t →
          ( t ·r (precompose-lifts P f h)) ∙h
          ( triangle-precompose-lifts' P refl-htpy h))
        ( inv (compute-tr-eq-htpy-fam-lifts P h f)))))

abstract
  coherence-triangle-precompose-lifts :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
    {f g : A → B} (H : f ~ g) → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P H
  coherence-triangle-precompose-lifts P {f} =
    ind-htpy f
      ( λ g H → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P H)
      ( coherence-triangle-precompose-lifts-refl-htpy P f)

  compute-coherence-triangle-precompose-lifts :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
    (f : A → B) →
      Id ( coherence-triangle-precompose-lifts P (refl-htpy' f))
          ( coherence-triangle-precompose-lifts-refl-htpy P f)
  compute-coherence-triangle-precompose-lifts P f =
    compute-ind-htpy f
      ( λ g H → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P H)
      ( coherence-triangle-precompose-lifts-refl-htpy P f)

total-lifts :
  {l1 l2 l3 : Level} (A : UU l1) {X : UU l2} (P : X → UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
total-lifts A {X} P = universally-structured-Π {A = A} {B = λ a → X} (λ a → P)

precompose-total-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) → (A → B) →
  total-lifts B P → total-lifts A P
precompose-total-lifts {A = A} P f =
  map-Σ
    ( λ h → (a : A) → P (h a))
    ( λ h → h ∘ f)
    ( precompose-lifts P f)

coherence-square-map-inv-distributive-Π-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) →
  coherence-square-maps
    ( precompose-total-lifts P f)
    ( map-inv-distributive-Π-Σ {A = B} {B = λ x → X} {C = λ x y → P y})
    ( map-inv-distributive-Π-Σ)
    ( λ h → h ∘ f)
coherence-square-map-inv-distributive-Π-Σ P f = refl-htpy
```

Our goal is now to produce a homotopy between `precompose-total-lifts P f` and
`precompose-total-lifts P g` for homotopic maps `f` and `g`, and a coherence
filling a cylinder.

```agda
HTPY-PRECOMPOSE-TOTAL-LIFTS :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) {f g : A → B} (H : f ~ g) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
HTPY-PRECOMPOSE-TOTAL-LIFTS P {f} {g} H =
  (precompose-total-lifts P f) ~ (precompose-total-lifts P g)

htpy-precompose-total-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  {f g : A → B} (H : f ~ g) → HTPY-PRECOMPOSE-TOTAL-LIFTS P H
htpy-precompose-total-lifts {A = A} {B} P {f} {g} H =
  htpy-map-Σ
    ( fam-lifts A P)
    ( λ h → eq-htpy (h ·l H))
    ( precompose-lifts P f)
    ( triangle-precompose-lifts P H)
```

We show that when `htpy-precompose-total-lifts` is applied to `refl-htpy`, it
computes to `refl-htpy`.

```agda
tr-id-left-subst :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {x y : A}
  (p : Id x y) (b : B) → (q : Id (f x) b) →
  Id (tr (λ (a : A) → Id (f a) b) p q) ((inv (ap f p)) ∙ q)
tr-id-left-subst refl b q = refl

compute-htpy-precompose-total-lifts :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  ( f : A → B) →
  ( htpy-precompose-total-lifts P (refl-htpy {f = f})) ~
  ( refl-htpy' (map-Σ (fam-lifts A P) (λ h → h ∘ f) (precompose-lifts P f)))
compute-htpy-precompose-total-lifts {A = A} P f (pair h h') =
  let α = λ (t : Id (h ∘ f) (h ∘ f)) → tr (fam-lifts A P) t (λ a → h' (f a))
  in
  ap eq-pair-Σ'
    ( eq-pair-Σ
      ( eq-htpy-refl-htpy (h ∘ f))
      ( ( tr-id-left-subst
          { f = α}
          ( eq-htpy-refl-htpy (h ∘ f))
          ( λ a → h' (f a))
          ( triangle-precompose-lifts P refl-htpy h h')) ∙
        ( ( ap
            ( λ t → inv (ap α (eq-htpy-refl-htpy (λ a → h (f a)))) ∙ t)
            ( htpy-eq
              ( htpy-eq (compute-triangle-precompose-lifts P f) h) h')) ∙
          ( left-inv (triangle-precompose-lifts-refl-htpy P f h h')))))

COHERENCE-INV-HTPY-DISTRIBUTIVE-Π-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  {f g : A → B} (H : f ~ g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
COHERENCE-INV-HTPY-DISTRIBUTIVE-Π-Σ P {f} {g} H =
  ( ( coherence-square-map-inv-distributive-Π-Σ P f) ∙h
    ( map-inv-distributive-Π-Σ ·l ( htpy-precompose-total-lifts P H))) ~
  ( ( ( λ h → eq-htpy (h ·l H)) ·r map-inv-distributive-Π-Σ) ∙h
    ( coherence-square-map-inv-distributive-Π-Σ P g))

coherence-inv-htpy-distributive-Π-Σ-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  (f : A → B) → COHERENCE-INV-HTPY-DISTRIBUTIVE-Π-Σ P (refl-htpy' f)
coherence-inv-htpy-distributive-Π-Σ-refl-htpy {X = X} P f =
  ( ap-concat-htpy
    ( coherence-square-map-inv-distributive-Π-Σ P f)
    ( λ h →
      ap
        ( ap map-inv-distributive-Π-Σ)
        ( compute-htpy-precompose-total-lifts P f h))) ∙h
  ( ap-concat-htpy'
    ( refl-htpy)
    ( inv-htpy
      ( λ h →
        compute-htpy-precomp-refl-htpy f (Σ X P) (map-inv-distributive-Π-Σ h))))

abstract
  coherence-inv-htpy-distributive-Π-Σ :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
    {f g : A → B} (H : f ~ g) → COHERENCE-INV-HTPY-DISTRIBUTIVE-Π-Σ P H
  coherence-inv-htpy-distributive-Π-Σ P {f} =
    ind-htpy f
      ( λ g H → COHERENCE-INV-HTPY-DISTRIBUTIVE-Π-Σ P H)
      ( coherence-inv-htpy-distributive-Π-Σ-refl-htpy P f)

module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  cone-family-dependent-pullback-property :
    {l : Level} (P : X → UU l) →
    cone-family
      ( fam-lifts (spanning-type-span-diagram 𝒮) P)
      ( precompose-lifts P (left-map-span-diagram 𝒮))
      ( precompose-lifts P (right-map-span-diagram 𝒮))
      ( cone-pullback-property-pushout 𝒮 c X)
      ( fam-lifts X P)
  cone-family-dependent-pullback-property P γ =
    pair
      ( precompose-lifts P (left-map-cocone-span-diagram 𝒮 c) γ)
      ( pair
        ( precompose-lifts P (right-map-cocone-span-diagram 𝒮 c) γ)
        ( triangle-precompose-lifts P
          ( coherence-square-cocone-span-diagram 𝒮 c)
          ( γ)))

  is-pullback-cone-family-dependent-pullback-property :
    pullback-property-pushout 𝒮 c →
    {l : Level} (P : X → UU l) (γ : X → X) →
    is-pullback
      ( ( tr
          ( fam-lifts (spanning-type-span-diagram 𝒮) P)
          ( eq-htpy (γ ·l (pr2 (pr2 c))))) ∘
        ( precompose-lifts P (left-map-span-diagram 𝒮) (γ ∘ (pr1 c))))
      ( precompose-lifts P (right-map-span-diagram 𝒮) (γ ∘ (pr1 (pr2 c))))
      ( cone-family-dependent-pullback-property P γ)
  is-pullback-cone-family-dependent-pullback-property pb-c P =
    is-pullback-family-is-pullback-tot
      ( fam-lifts (spanning-type-span-diagram 𝒮) P)
      ( precompose-lifts P (left-map-span-diagram 𝒮))
      ( precompose-lifts P (right-map-span-diagram 𝒮))
      ( cone-pullback-property-pushout 𝒮 c X)
      ( cone-family-dependent-pullback-property P)
      ( pb-c X)
      ( is-pullback-top-is-pullback-bottom-cube-is-equiv
        ( precomp (left-map-cocone-span-diagram 𝒮 c) (Σ X P))
        ( precomp (right-map-cocone-span-diagram 𝒮 c) (Σ X P))
        ( precomp (left-map-span-diagram 𝒮) (Σ X P))
        ( precomp (right-map-span-diagram 𝒮) (Σ X P))
        ( map-Σ
          ( fam-lifts (domain-span-diagram 𝒮) P)
          ( precomp (left-map-cocone-span-diagram 𝒮 c) X)
          ( precompose-lifts P (left-map-cocone-span-diagram 𝒮 c)))
        ( map-Σ
          ( fam-lifts (codomain-span-diagram 𝒮) P)
          ( precomp (right-map-cocone-span-diagram 𝒮 c) X)
          ( precompose-lifts P (right-map-cocone-span-diagram 𝒮 c)))
        ( map-Σ
          ( fam-lifts (spanning-type-span-diagram 𝒮) P)
          ( precomp (left-map-span-diagram 𝒮) X)
          ( precompose-lifts P (left-map-span-diagram 𝒮)))
        ( map-Σ
          ( fam-lifts (spanning-type-span-diagram 𝒮) P)
          ( precomp (right-map-span-diagram 𝒮) X)
          ( precompose-lifts P (right-map-span-diagram 𝒮)))
        ( map-inv-distributive-Π-Σ)
        ( map-inv-distributive-Π-Σ)
        ( map-inv-distributive-Π-Σ)
        ( map-inv-distributive-Π-Σ)
        ( htpy-precompose-total-lifts P
          ( coherence-square-cocone-span-diagram 𝒮 c))
        ( refl-htpy)
        ( refl-htpy)
        ( refl-htpy)
        ( refl-htpy)
        ( htpy-precomp (coherence-square-cocone-span-diagram 𝒮 c) (Σ X P))
        ( coherence-inv-htpy-distributive-Π-Σ P
          ( coherence-square-cocone-span-diagram 𝒮 c))
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( pb-c (Σ X P)))

  dependent-pullback-property-pullback-property-pushout :
    pullback-property-pushout 𝒮 c →
    dependent-pullback-property-pushout 𝒮 c
  dependent-pullback-property-pullback-property-pushout pullback-c P =
    is-pullback-htpy'
      ( ( tr-eq-htpy-fam-lifts P
          ( id)
          ( coherence-square-cocone-span-diagram 𝒮 c)) ·r
        ( precompose-lifts P
          ( left-map-span-diagram 𝒮)
          ( left-map-cocone-span-diagram 𝒮 c)))
      ( refl-htpy)
      ( cone-family-dependent-pullback-property P id)
      { c' = cone-dependent-pullback-property-pushout 𝒮 c P}
      ( pair
        ( refl-htpy)
        ( pair
          ( refl-htpy)
          ( ( right-unit-htpy) ∙h
            ( coherence-triangle-precompose-lifts P
              ( coherence-square-cocone-span-diagram 𝒮 c)
              ( id)))))
      ( is-pullback-cone-family-dependent-pullback-property pullback-c P id)
```

This concludes the proof of Theorem 18.1.4.

We give some further useful implications.

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  dependent-universal-property-universal-property-pushout :
    universal-property-pushout 𝒮 c →
    dependent-universal-property-pushout 𝒮 c
  dependent-universal-property-universal-property-pushout up-X =
    dependent-universal-property-dependent-pullback-property-pushout 𝒮 c
      ( dependent-pullback-property-pullback-property-pushout 𝒮 c
        ( pullback-property-pushout-universal-property-pushout 𝒮 c up-X))
```

## Section 18.3 The Flattening lemma for pushouts

### Definition 18.3.1

```agda
{-
cocone-flattening-pushout :
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X)
  ( P : Fam-pushout l5 f g)
  ( Q : X → UU l5)
  ( e : equiv-Fam-pushout P (desc-fam f g c Q)) →
  cocone
    ( map-Σ (pr1 P) f (λ _ → id))
    ( map-Σ (pr1 (pr2 P)) g (λ x → map-equiv (pr2 (pr2 P) x)))
    ( Σ X Q)
cocone-flattening-pushout f g c P Q e =
  pair
    ( map-Σ Q
      ( pr1 c)
      ( λ a → map-equiv (pr1 e a)))
    ( pair
      ( map-Σ Q
        ( pr1 (pr2 c))
        ( λ b → map-equiv (pr1 (pr2 e) b)))
      ( htpy-map-Σ Q
        ( pr2 (pr2 c))
        ( λ x → map-equiv (pr1 e (f x)))
        ( λ x → inv-htpy (pr2 (pr2 e) x))))
-}
```

### Theorem 18.3.2 The flattening lemma

```agda
{-
coherence-bottom-flattening-lemma' :
  {l1 l2 l3 : Level} {B : UU l1} {Q : B → UU l2} {T : UU l3}
  {b b' : B} (α : Id b b') {y : Q b} {y' : Q b'} (β : Id (tr Q α y) y')
  (h : (b : B) → Q b → T) → Id (h b y) (h b' y')
coherence-bottom-flattening-lemma' refl refl h = refl

coherence-bottom-flattening-lemma :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {P : A → UU l3} {Q : B → UU l4} {T : UU l5}
  {f f' : A → B} (H : f ~ f')
  {g : (a : A) → P a → Q (f a)}
  {g' : (a : A) → P a → Q (f' a)}
  (K : (a : A) → ((tr Q (H a)) ∘ (g a)) ~ (g' a))
  (h : (b : B) → Q b → T) → (a : A) (p : P a) →
  Id (h (f a) (g a p)) (h (f' a) (g' a p))
coherence-bottom-flattening-lemma H K h a p =
  coherence-bottom-flattening-lemma' (H a) (K a p) h
coherence-cube-flattening-lemma :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {P : A → UU l3} {Q : B → UU l4} {T : UU l5}
  {f f' : A → B} (H : f ~ f')
  {g : (a : A) → P a → Q (f a)}
  {g' : (a : A) → P a → Q (f' a)}
  (K : (a : A) → ((tr Q (H a)) ∘ (g a)) ~ (g' a))
  (h : Σ B Q → T) →
  Id ( eq-htpy
       ( λ a → eq-htpy
         ( coherence-bottom-flattening-lemma H K (ev-pair h) a)))
     ( ap ev-pair
       ( htpy-precomp (htpy-map-Σ Q H g K) T h))
coherence-cube-flattening-lemma
  {A = A} {B} {P} {Q} {T} {f = f} {f'} H {g} {g'} K =
  ind-htpy f
    ( λ f' H' →
      (g : (a : A) → P a → Q (f a)) (g' : (a : A) → P a → Q (f' a))
      (K : (a : A) → ((tr Q (H' a)) ∘ (g a)) ~ (g' a)) (h : Σ B Q → T) →
      Id ( eq-htpy
           ( λ a → eq-htpy
             ( coherence-bottom-flattening-lemma H' K (ev-pair h) a)))
         ( ap ev-pair
           ( htpy-precomp (htpy-map-Σ Q H' g K) T h)))
    ( λ g g' K h → {!ind-htpy g (λ g' K' → (h : Σ B Q → T) →
      Id ( eq-htpy
           ( λ a → eq-htpy
             ( coherence-bottom-flattening-lemma
                refl-htpy (λ a → htpy-eq (K' a)) (ev-pair h) a)))
         ( ap ev-pair
           ( htpy-precomp
              ( htpy-map-Σ Q refl-htpy g
                (λ a → htpy-eq (K' a))) T h))) ? (λ a → eq-htpy (K a)) h!})
    H g g' K

flattening-pushout' :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ( P : Fam-pushout l5 f g)
  ( Q : X → UU l5)
  ( e : equiv-Fam-pushout P (desc-fam f g c Q)) →
  (l : Level) →
  pullback-property-pushout l
    ( map-Σ (pr1 P) f (λ _ → id))
    ( map-Σ (pr1 (pr2 P)) g (λ x → map-equiv (pr2 (pr2 P) x)))
    ( cocone-flattening-pushout f g c P Q e)
flattening-pushout' f g c P Q e l T =
  is-pullback-top-is-pullback-bottom-cube-is-equiv
    ( ( map-Π (λ x → precomp-Π (map-equiv (pr1 e x)) (λ q → T))) ∘
      ( precomp-Π (pr1 c) (λ x → (Q x) → T)))
    ( ( map-Π (λ x → precomp-Π (map-equiv (pr1 (pr2 e) x)) (λ q → T))) ∘
      ( precomp-Π (pr1 (pr2 c)) (λ x → (Q x) → T)))
    ( precomp-Π f (λ a → (pr1 P a) → T))
    ( ( map-Π (λ x → precomp (map-equiv (pr2 (pr2 P) x)) T)) ∘
      ( precomp-Π g (λ b → (pr1 (pr2 P) b) → T)))
    ( precomp (map-Σ Q (pr1 c) (λ a → map-equiv (pr1 e a))) T)
    ( precomp (map-Σ Q (pr1 (pr2 c)) (λ b → map-equiv (pr1 (pr2 e) b))) T)
    ( precomp (map-Σ (pr1 P) f (λ _ → id)) T)
    ( precomp (map-Σ (pr1 (pr2 P)) g (λ x → map-equiv (pr2 (pr2 P) x))) T)
    ev-pair
    ev-pair
    ev-pair
    ev-pair
    ( htpy-precomp
      ( htpy-map-Σ Q
        ( pr2 (pr2 c))
        ( λ x → map-equiv (pr1 e (f x)))
        ( λ x → inv-htpy (pr2 (pr2 e) x)))
      ( T))
    refl-htpy
    refl-htpy
    refl-htpy
    refl-htpy
    ( λ h →
      eq-htpy
        ( λ x →
          eq-htpy
            ( coherence-bottom-flattening-lemma
              ( pr2 (pr2 c))
              ( λ y → inv-htpy (pr2 (pr2 e) y))
              ( h)
              ( x))))
    {!!}
    is-equiv-ev-pair
    is-equiv-ev-pair
    is-equiv-ev-pair
    is-equiv-ev-pair
    {!!}

flattening-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ( P : Fam-pushout l5 f g)
  ( Q : X → UU l5)
  ( e : equiv-Fam-pushout P (desc-fam f g c Q)) →
  (l : Level) →
  universal-property-pushout l
    ( map-Σ (pr1 P) f (λ _ → id))
    ( map-Σ (pr1 (pr2 P)) g (λ x → map-equiv (pr2 (pr2 P) x)))
    ( cocone-flattening-pushout f g c P Q e)
flattening-pushout f g c P Q e l =
  universal-property-pushout-pullback-property-pushout l
    ( map-Σ (pr1 P) f (λ _ → id))
    ( map-Σ (pr1 (pr2 P)) g (λ x → map-equiv (pr2 (pr2 P) x)))
    ( cocone-flattening-pushout f g c P Q e)
    ( flattening-pushout' f g c P Q e l)
-}
```
