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
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-pullback-property-pushouts
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.pullback-property-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Section 16.2 Families over pushouts

### Definition 18.2.1

```agda
Fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
Fam-pushout l {S} {A} {B} f g =
  Σ ( A → UU l)
    ( λ PA → Σ (B → UU l)
      ( λ PB → (s : S) → PA (f s) ≃ PB (g s)))
```

### Characterizing the identity type of `Fam-pushout`

```agda
coherence-equiv-Fam-pushout :
  { l1 l2 l3 l l' : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B}
  ( P : Fam-pushout l f g) (Q : Fam-pushout l' f g) →
  ( eA : (a : A) → (pr1 P a) ≃ (pr1 Q a))
  ( eB : (b : B) → (pr1 (pr2 P) b) ≃ (pr1 (pr2 Q) b)) →
  UU (l1 ⊔ l ⊔ l')
coherence-equiv-Fam-pushout {S = S} {f = f} {g} P Q eA eB =
  ( s : S) →
    ( (map-equiv (eB (g s))) ∘ (map-equiv (pr2 (pr2 P) s))) ~
    ( (map-equiv (pr2 (pr2 Q) s)) ∘ (map-equiv (eA (f s))))

equiv-Fam-pushout :
  {l1 l2 l3 l l' : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} →
  Fam-pushout l f g → Fam-pushout l' f g → UU (l1 ⊔ l2 ⊔ l3 ⊔ l ⊔ l')
equiv-Fam-pushout {S = S} {A} {B} {f} {g} P Q =
  Σ ( (a : A) → (pr1 P a) ≃ (pr1 Q a)) ( λ eA →
    Σ ( (b : B) → (pr1 (pr2 P) b) ≃ (pr1 (pr2 Q) b))
      ( coherence-equiv-Fam-pushout P Q eA))

reflexive-equiv-Fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} (P : Fam-pushout l f g) →
  equiv-Fam-pushout P P
reflexive-equiv-Fam-pushout (pair PA (pair PB PS)) =
  pair
    ( λ a → id-equiv)
    ( pair
      ( λ b → id-equiv)
      ( λ s → refl-htpy))

equiv-Fam-pushout-eq :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} {P Q : Fam-pushout l f g} →
  Id P Q → equiv-Fam-pushout P Q
equiv-Fam-pushout-eq {P = P} {.P} refl =
  reflexive-equiv-Fam-pushout P

is-torsorial-equiv-Fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} (P : Fam-pushout l f g) →
  is-torsorial (equiv-Fam-pushout P)
is-torsorial-equiv-Fam-pushout {S = S} {A} {B} {f} {g} P =
  is-torsorial-Eq-structure
    ( is-torsorial-Eq-Π (λ a → is-torsorial-equiv (pr1 P a)))
    ( pair (pr1 P) (λ a → id-equiv))
    ( is-torsorial-Eq-structure
      ( is-torsorial-Eq-Π (λ b → is-torsorial-equiv (pr1 (pr2 P) b)))
      ( pair (pr1 (pr2 P)) (λ b → id-equiv))
      ( is-torsorial-Eq-Π (λ s → is-torsorial-htpy-equiv (pr2 (pr2 P) s))))

is-equiv-equiv-Fam-pushout-eq :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} (P Q : Fam-pushout l f g) →
  is-equiv (equiv-Fam-pushout-eq {P = P} {Q})
is-equiv-equiv-Fam-pushout-eq P =
  fundamental-theorem-id
    ( is-torsorial-equiv-Fam-pushout P)
    ( λ Q → equiv-Fam-pushout-eq {P = P} {Q})

equiv-equiv-Fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} (P Q : Fam-pushout l f g) →
  Id P Q ≃ equiv-Fam-pushout P Q
equiv-equiv-Fam-pushout P Q =
  pair
    ( equiv-Fam-pushout-eq)
    ( is-equiv-equiv-Fam-pushout-eq P Q)

eq-equiv-Fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} {P Q : Fam-pushout l f g} →
  (equiv-Fam-pushout P Q) → Id P Q
eq-equiv-Fam-pushout {P = P} {Q} =
  map-inv-is-equiv (is-equiv-equiv-Fam-pushout-eq P Q)

is-section-eq-equiv-Fam-pushout :
  { l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} {P Q : Fam-pushout l f g} →
  ( ( equiv-Fam-pushout-eq {P = P} {Q}) ∘
    ( eq-equiv-Fam-pushout {P = P} {Q})) ~ id
is-section-eq-equiv-Fam-pushout {P = P} {Q} =
  is-section-map-inv-is-equiv (is-equiv-equiv-Fam-pushout-eq P Q)

is-retraction-eq-equiv-Fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} {P Q : Fam-pushout l f g} →
  ( ( eq-equiv-Fam-pushout {P = P} {Q}) ∘
    ( equiv-Fam-pushout-eq {P = P} {Q})) ~ id
is-retraction-eq-equiv-Fam-pushout {P = P} {Q} =
  is-retraction-map-inv-is-equiv (is-equiv-equiv-Fam-pushout-eq P Q)
```

This concludes the characterization of the identity type of `Fam-pushout`.

### Definition 18.2.2

```agda
desc-fam :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  {f : S → A} {g : S → B} (c : cocone f g X) →
  (P : X → UU l) → Fam-pushout l f g
desc-fam c P =
  pair
    ( P ∘ (pr1 c))
    ( pair
      ( P ∘ (pr1 (pr2 c)))
      ( λ s → (pair (tr P (pr2 (pr2 c) s)) (is-equiv-tr P (pr2 (pr2 c) s)))))
```

### Theorem 18.2.3

```agda
Fam-pushout-cocone-UU :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} → cocone f g (UU l) → Fam-pushout l f g
Fam-pushout-cocone-UU l =
  tot (λ PA → (tot (λ PB H s → equiv-eq (H s))))

is-equiv-Fam-pushout-cocone-UU :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  {f : S → A} {g : S → B} →
  is-equiv (Fam-pushout-cocone-UU l {f = f} {g})
is-equiv-Fam-pushout-cocone-UU l {f = f} {g} =
  is-equiv-tot-is-fiberwise-equiv
    ( λ PA →
      is-equiv-tot-is-fiberwise-equiv
        ( λ PB →
          is-equiv-map-Π-is-fiberwise-equiv
            ( λ s → univalence (PA (f s)) (PB (g s)))))

htpy-equiv-eq-ap-fam :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A} (p : Id x y) →
  htpy-equiv (equiv-tr B p) (equiv-eq (ap B p))
htpy-equiv-eq-ap-fam B {x} {.x} refl =
  refl-htpy-equiv id-equiv

triangle-desc-fam :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  {f : S → A} {g : S → B} (c : cocone f g X) →
  ( desc-fam {l = l} c) ~
  ( ( Fam-pushout-cocone-UU l {f = f} {g}) ∘ ( cocone-map f g {Y = UU l} c))
triangle-desc-fam {l = l} {S} {A} {B} {X} (pair i (pair j H)) P =
  eq-equiv-Fam-pushout
    ( pair
      ( λ a → id-equiv)
      ( pair
        ( λ b → id-equiv)
        ( λ s → htpy-equiv-eq-ap-fam P (H s))))

is-equiv-desc-fam :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  {f : S → A} {g : S → B} (c : cocone f g X) →
  universal-property-pushout f g c →
  is-equiv (desc-fam {l = l} {f = f} {g} c)
is-equiv-desc-fam {l = l} {f = f} {g} c up-c =
  is-equiv-left-map-triangle
    ( desc-fam c)
    ( Fam-pushout-cocone-UU l)
    ( cocone-map f g c)
    ( triangle-desc-fam c)
    ( up-c (UU l))
    ( is-equiv-Fam-pushout-cocone-UU l)

equiv-desc-fam :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  {f : S → A} {g : S → B} (c : cocone f g X) →
  universal-property-pushout f g c →
  (X → UU l) ≃ Fam-pushout l f g
equiv-desc-fam c up-c =
  pair
    ( desc-fam c)
    ( is-equiv-desc-fam c up-c)
```

### Corollary 18.2.4

```agda
uniqueness-Fam-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  universal-property-pushout f g c →
  ( P : Fam-pushout l f g) →
  is-contr
    ( Σ (X → UU l) (λ Q →
      equiv-Fam-pushout P (desc-fam c Q)))
uniqueness-Fam-pushout {l = l} f g c up-c P =
  is-contr-equiv'
    ( fiber (desc-fam c) P)
    ( equiv-tot (λ Q →
      ( equiv-equiv-Fam-pushout P (desc-fam c Q)) ∘e
      ( equiv-inv (desc-fam c Q) P)))
    ( is-contr-map-is-equiv (is-equiv-desc-fam c up-c) P)

fam-Fam-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  {f : S → A} {g : S → B} (c : cocone f g X) →
  universal-property-pushout f g c →
  Fam-pushout l f g → X → UU l
fam-Fam-pushout {f = f} {g} c up-X P =
  pr1 (center (uniqueness-Fam-pushout f g c up-X P))

is-section-fam-Fam-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  {f : S → A} {g : S → B} (c : cocone f g X) →
  (up-X : universal-property-pushout f g c) →
  desc-fam {l = l} c ∘ fam-Fam-pushout c up-X ~ id
is-section-fam-Fam-pushout {f = f} {g} c up-X P =
  inv
    ( eq-equiv-Fam-pushout (pr2 (center (uniqueness-Fam-pushout f g c up-X P))))

compute-left-fam-Fam-pushout :
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : universal-property-pushout f g c) →
  ( P : Fam-pushout l f g) →
  ( a : A) → (pr1 P a) ≃ (fam-Fam-pushout c up-X P (pr1 c a))
compute-left-fam-Fam-pushout {f = f} {g} c up-X P =
  pr1 (pr2 (center (uniqueness-Fam-pushout f g c up-X P)))

compute-right-fam-Fam-pushout :
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : universal-property-pushout f g c) →
  ( P : Fam-pushout l f g) →
  ( b : B) → (pr1 (pr2 P) b) ≃ (fam-Fam-pushout c up-X P (pr1 (pr2 c) b))
compute-right-fam-Fam-pushout {f = f} {g} c up-X P =
  pr1 (pr2 (pr2 (center (uniqueness-Fam-pushout f g c up-X P))))

compute-path-fam-Fam-pushout :
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : universal-property-pushout f g c) →
  ( P : Fam-pushout l f g) →
  ( s : S) →
    ( ( map-equiv (compute-right-fam-Fam-pushout c up-X P (g s))) ∘
      ( map-equiv (pr2 (pr2 P) s))) ~
    ( ( tr (fam-Fam-pushout c up-X P) (pr2 (pr2 c) s)) ∘
      ( map-equiv (compute-left-fam-Fam-pushout c up-X P (f s))))
compute-path-fam-Fam-pushout {f = f} {g} c up-X P =
  pr2 (pr2 (pr2 (center (uniqueness-Fam-pushout f g c up-X P))))
```
