# The descent property of the circle

```agda
module synthetic-homotopy-theory.descent-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

## Idea

The descent property uniquely characterizes type families over the circle.

## Definitions

```agda
Fam-circle :
  ( l1 : Level) → UU (lsuc l1)
Fam-circle l1 = Σ (UU l1) Aut
```

## Properties

### Characterization of the identity type of `Fam-circle`

```agda
Eq-Fam-circle :
  { l1 : Level} → Fam-circle l1 → Fam-circle l1 → UU l1
Eq-Fam-circle P Q =
  Σ ( (pr1 P) ≃ (pr1 Q))
    ( λ h →
      ( (map-equiv h) ∘ (map-equiv (pr2 P))) ~ ((map-equiv (pr2 Q)) ∘ (map-equiv h)))

reflexive-Eq-Fam-circle :
  { l1 : Level} (P : Fam-circle l1) → Eq-Fam-circle P P
reflexive-Eq-Fam-circle (pair X e) =
  pair id-equiv refl-htpy

Eq-Fam-circle-eq :
  { l1 : Level} (P Q : Fam-circle l1) → Id P Q → Eq-Fam-circle P Q
Eq-Fam-circle-eq P .P refl = reflexive-Eq-Fam-circle P

is-contr-total-Eq-Fam-circle :
  { l1 : Level} (P : Fam-circle l1) →
  is-contr (Σ (Fam-circle l1) (Eq-Fam-circle P))
is-contr-total-Eq-Fam-circle (pair X e) =
  is-contr-total-Eq-structure
    ( λ Y f h →
      ((map-equiv h) ∘ (map-equiv e)) ~ ((map-equiv f) ∘ (map-equiv h)))
    ( is-contr-total-equiv X)
    ( pair X id-equiv)
  ( is-contr-total-htpy-equiv e)

is-equiv-Eq-Fam-circle-eq :
  { l1 : Level} (P Q : Fam-circle l1) → is-equiv (Eq-Fam-circle-eq P Q)
is-equiv-Eq-Fam-circle-eq P =
  fundamental-theorem-id
    ( is-contr-total-Eq-Fam-circle P)
    ( Eq-Fam-circle-eq P)

eq-Eq-Fam-circle :
  { l1 : Level} (P Q : Fam-circle l1) → Eq-Fam-circle P Q → Id P Q
eq-Eq-Fam-circle P Q = map-inv-is-equiv (is-equiv-Eq-Fam-circle-eq P Q)
```

### Uniqueness of type families defined by `Fam-circle`

```agda
ev-fam-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loop X) →
  ( X → UU l2) → Fam-circle l2
ev-fam-circle l P =
  pair
    ( P (base-free-loop l))
    ( equiv-tr P (loop-free-loop l))

comparison-fam-circle :
  ( l1 : Level) → free-loop (UU l1) → Fam-circle l1
comparison-fam-circle l1 = tot (λ Y → equiv-eq)

is-equiv-comparison-fam-circle :
  ( l1 : Level) → is-equiv (comparison-fam-circle l1)
is-equiv-comparison-fam-circle l1 =
  is-equiv-tot-is-fiberwise-equiv (λ Y → univalence Y Y)

triangle-comparison-fam-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loop X) →
  (ev-fam-circle l) ~ ((comparison-fam-circle l2) ∘ (ev-free-loop l (UU l2)))
triangle-comparison-fam-circle l P =
  eq-Eq-Fam-circle
    ( ev-fam-circle l P)
    ( comparison-fam-circle _ (ev-free-loop l (UU _) P))
    ( pair id-equiv (htpy-eq (inv (tr-equiv-eq-ap (pr2 l)))))

is-equiv-ev-fam-circle-universal-property-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  ( up-circle : universal-property-circle (lsuc l2) l) →
  is-equiv (ev-fam-circle {l2 = l2} l)
is-equiv-ev-fam-circle-universal-property-circle {l2 = l2} l up-circle =
  is-equiv-comp-htpy
    ( ev-fam-circle l)
    ( comparison-fam-circle l2)
    ( ev-free-loop l (UU l2))
    ( triangle-comparison-fam-circle l)
    ( up-circle (UU l2))
    ( is-equiv-comparison-fam-circle l2)

unique-family-property-circle :
  { l1 : Level} (l2 : Level) {X : UU l1} (l : free-loop X) →
  UU (l1 ⊔ lsuc l2)
unique-family-property-circle l2 {X} l =
  ( Q : Fam-circle l2) →
    is-contr (Σ (X → UU l2) (λ P → Eq-Fam-circle Q (ev-fam-circle l P)))

unique-family-property-universal-property-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loop X) →
  universal-property-circle (lsuc l2) l → unique-family-property-circle l2 l
unique-family-property-universal-property-circle l up-circle Q =
  is-contr-is-equiv'
    ( fib (ev-fam-circle l) Q)
    ( tot (λ P → (Eq-Fam-circle-eq Q (ev-fam-circle l P)) ∘ inv))
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ P →
        is-equiv-comp _ _
          ( is-equiv-inv _ _)
          ( is-equiv-Eq-Fam-circle-eq Q (ev-fam-circle l P))))
    ( is-contr-map-is-equiv
      ( is-equiv-ev-fam-circle-universal-property-circle l up-circle)
      ( Q))
```

### Sections of families over the circle

```agda
Section-Fam-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loop X) (P : Fam-circle l2) → UU _
Section-Fam-circle l P =
  Σ (pr1 P) (λ p → Id (map-equiv (pr2 P) p) p)

fam-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loop X) →
  ( {k : Level} → dependent-universal-property-circle k l) →
  Fam-circle l2 → X → UU l2
fam-circle {l1} {l2} l dup-circle =
  map-inv-is-equiv
    ( is-equiv-ev-fam-circle-universal-property-circle l
      ( universal-property-dependent-universal-property-circle l dup-circle))

section-fam-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l2 l) →
  ( Q : X → UU l2) (P : Fam-circle l2) →
  ( e : Eq-Fam-circle P (ev-fam-circle l Q)) →
  Section-Fam-circle l P → (x : X) → Q x
section-fam-circle l dup-circle Q P (pair e H) (pair p α) =
  map-inv-is-equiv
    ( dup-circle Q)
    ( pair (map-equiv e p) ((inv (H p)) ∙ (ap (map-equiv e) α)))
```
