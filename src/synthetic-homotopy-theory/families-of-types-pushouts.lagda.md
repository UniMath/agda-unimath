# Descent for pushouts

```agda
module synthetic-homotopy-theory.families-of-types-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.torsorial-type-families

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.operations-cocones-under-span-diagrams
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

Consider a [pushout square](synthetic-homotopy-theory.pushouts.md)

```text
        g
    S -----> B
    |        |
  f |        | j
    V      ⌜ V
    A -----> X.
        i
```

Then the
[universal property of the pushout](synthetic-homotopy-theory.universal-property-pushouts.md)
implies that the left map in the
[triangle](foundation-core.commuting-triangles-of-maps.md)

```text
           (X → 𝒰)
          /       \
       ≃ /         \
        ∨           ∨
  cocone s 𝒰 --> Σ (P : A → 𝒰) (Q : B → 𝒰), Π (x : S) → P (f x) ≃ Q (g x)
              ≃
```

is an [equivalence](foundation-core.equivalences.md). By the
[univalence axiom](foundation.univalence.md) it follows that the bottom map is
an equivalence. Therefore it follows that a type family over `X` is equivalently
described as the {{#concept "structure of a type family over a pushout"}}, which
consists of triples `(P , Q , e)` consisting of

```text
  P : A → 𝒰
  Q : B → 𝒰
  e : Π (x : S) → P (f x) ≃ Q (g x).
```

In other words, for any such triple `(P , Q , e)`, the type of families
`Y : X → 𝒰` equipped with
[families of equivalences](foundation.families-of-equivalences.md)

```text
  u : (a : A) → P a ≃ Y (i a)
  v : (b : B) → Q b ≃ Y (j b)
```

and a family of [homotopies](foundation-core.homotopies.md) witnessing that the
square of equivalences

```text
             u (f x)
    P (f x) --------> Y (i (f x))
      |                   |
  e x |                   | tr Y (H x)
      V                   V
    Q (g x) --------> Y (j (g x))
             v (g x)
```

[commutes](foundation-core.commuting-squares-of-maps.md) for each `x : S` is
[contractible](foundation-core.contractible-types.md).

## Definitions

### The structure of type families over pushouts

**Note.** In the definition of structure of type families over pushouts we will
assume that the families `A → 𝒰` and `B → 𝒰` are of the same
[universe level](foundation.universe-levels.md).

```agda
module _
  {l1 l2 l3 : Level} (l : Level) (s : span-diagram l1 l2 l3)
  where

  structure-type-family-pushout : UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
  structure-type-family-pushout =
    Σ ( domain-span-diagram s → UU l)
      ( λ PA →
        Σ ( codomain-span-diagram s → UU l)
          ( λ PB →
            (x : spanning-type-span-diagram s) →
            PA (left-map-span-diagram s x) ≃ PB (right-map-span-diagram s x)))

module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 s)
  where

  left-type-family-structure-type-family-pushout :
    domain-span-diagram s → UU l4
  left-type-family-structure-type-family-pushout = pr1 P

  right-type-family-structure-type-family-pushout :
    codomain-span-diagram s → UU l4
  right-type-family-structure-type-family-pushout = pr1 (pr2 P)

  matching-equiv-structure-type-family-pushout :
    (x : spanning-type-span-diagram s) →
    left-type-family-structure-type-family-pushout (left-map-span-diagram s x) ≃
    right-type-family-structure-type-family-pushout (right-map-span-diagram s x)
  matching-equiv-structure-type-family-pushout = pr2 (pr2 P)

  map-matching-equiv-structure-type-family-pushout :
    (x : spanning-type-span-diagram s) →
    left-type-family-structure-type-family-pushout (left-map-span-diagram s x) →
    right-type-family-structure-type-family-pushout (right-map-span-diagram s x)
  map-matching-equiv-structure-type-family-pushout x =
    map-equiv (matching-equiv-structure-type-family-pushout x)
```

### The structure of a type family over a pushout obtained from a type family over a cocone

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X)
  (P : X → UU l5)
  where

  left-type-family-structure-type-family-pushout-type-family :
    domain-span-diagram s → UU l5
  left-type-family-structure-type-family-pushout-type-family =
    P ∘ left-map-cocone-span-diagram s c

  right-type-family-structure-type-family-pushout-type-family :
    codomain-span-diagram s → UU l5
  right-type-family-structure-type-family-pushout-type-family =
    P ∘ right-map-cocone-span-diagram s c

  matching-equiv-structure-type-family-pushout-type-family :
    (x : spanning-type-span-diagram s) →
    left-type-family-structure-type-family-pushout-type-family
      ( left-map-span-diagram s x) ≃
    right-type-family-structure-type-family-pushout-type-family
      ( right-map-span-diagram s x)
  matching-equiv-structure-type-family-pushout-type-family x =
    equiv-tr P (coherence-square-cocone-span-diagram s c x)

  structure-type-family-pushout-type-family :
    structure-type-family-pushout l5 s
  pr1 structure-type-family-pushout-type-family =
    left-type-family-structure-type-family-pushout-type-family
  pr1 (pr2 structure-type-family-pushout-type-family) =
    right-type-family-structure-type-family-pushout-type-family
  pr2 (pr2 structure-type-family-pushout-type-family) =
    matching-equiv-structure-type-family-pushout-type-family
```

### Equivalences of type family structures over pushouts

Consider two structures `(PA , PB , Pe)` and (QA , QB , Qe)` of type families
over a span diagram

```text
        g
    S -----> B
    |
  f |
    V
    A
```

An {{#concept "equivalence of structures of type families over pushouts"}}
consists of families of equivalences

```text
  u : (a : A) → PA a ≃ QA a
  v : (b : B) → PB b ≃ QB b
```

and a family of homotopies witnessing that the square

```text
               u (f x)
     PA (f x) --------> QA (f x)
       |                  |
  Pe x |                  | Qe x
       V                  V
     PB (g x) --------> QB (g x)
               v (g x)
```

commutes for each `x : S`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 s)
  (Q : structure-type-family-pushout l5 s)
  where

  equiv-left-type-family-structure-type-family-pushout : UU (l1 ⊔ l4 ⊔ l5)
  equiv-left-type-family-structure-type-family-pushout =
    (a : domain-span-diagram s) →
    left-type-family-structure-type-family-pushout s P a ≃
    left-type-family-structure-type-family-pushout s Q a

  equiv-right-type-family-structure-type-family-pushout : UU (l2 ⊔ l4 ⊔ l5)
  equiv-right-type-family-structure-type-family-pushout =
    (b : codomain-span-diagram s) →
    right-type-family-structure-type-family-pushout s P b ≃
    right-type-family-structure-type-family-pushout s Q b

  coherence-square-equiv-structure-type-family-pushout :
    equiv-left-type-family-structure-type-family-pushout →
    equiv-right-type-family-structure-type-family-pushout →
    UU (l3 ⊔ l4 ⊔ l5)
  coherence-square-equiv-structure-type-family-pushout eA eB =
    ( x : spanning-type-span-diagram s) →
    coherence-square-maps
      ( map-equiv (eA (left-map-span-diagram s x)))
      ( map-equiv (pr2 (pr2 P) x))
      ( map-equiv (pr2 (pr2 Q) x))
      ( map-equiv (eB (right-map-span-diagram s x)))

  equiv-structure-type-family-pushout :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  equiv-structure-type-family-pushout =
    Σ ( equiv-left-type-family-structure-type-family-pushout)
      ( λ eA →
        Σ ( equiv-right-type-family-structure-type-family-pushout)
          ( coherence-square-equiv-structure-type-family-pushout eA))

  left-equiv-equiv-structure-type-family-pushout :
    equiv-structure-type-family-pushout →
    equiv-left-type-family-structure-type-family-pushout
  left-equiv-equiv-structure-type-family-pushout = pr1

  map-left-equiv-equiv-structure-type-family-pushout :
    equiv-structure-type-family-pushout →
    (a : domain-span-diagram s) →
    left-type-family-structure-type-family-pushout s P a →
    left-type-family-structure-type-family-pushout s Q a
  map-left-equiv-equiv-structure-type-family-pushout e a =
    map-equiv (left-equiv-equiv-structure-type-family-pushout e a)

  right-equiv-equiv-structure-type-family-pushout :
    equiv-structure-type-family-pushout →
    equiv-right-type-family-structure-type-family-pushout
  right-equiv-equiv-structure-type-family-pushout = pr1 ∘ pr2

  map-right-equiv-equiv-structure-type-family-pushout :
    equiv-structure-type-family-pushout →
    (b : codomain-span-diagram s) →
    right-type-family-structure-type-family-pushout s P b →
    right-type-family-structure-type-family-pushout s Q b
  map-right-equiv-equiv-structure-type-family-pushout e b =
    map-equiv (right-equiv-equiv-structure-type-family-pushout e b)

  coherence-equiv-structure-type-family-pushout :
    (e : equiv-structure-type-family-pushout) →
    coherence-square-equiv-structure-type-family-pushout
      ( left-equiv-equiv-structure-type-family-pushout e)
      ( right-equiv-equiv-structure-type-family-pushout e)
  coherence-equiv-structure-type-family-pushout = pr2 ∘ pr2
```

### Identity equivalences of type family structures over pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 s)
  where

  id-equiv-structure-type-family-pushout :
    equiv-structure-type-family-pushout s P P
  pr1 id-equiv-structure-type-family-pushout a = id-equiv
  pr1 (pr2 id-equiv-structure-type-family-pushout) b = id-equiv
  pr2 (pr2 id-equiv-structure-type-family-pushout) x = refl-htpy
```

## Properties

### Characterization of the identity type of the type of structures of type families over pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 s)
  where

  equiv-eq-structure-type-family-pushout :
    (Q : structure-type-family-pushout l4 s) →
    P ＝ Q → equiv-structure-type-family-pushout s P Q
  equiv-eq-structure-type-family-pushout .P refl =
    id-equiv-structure-type-family-pushout s P

  is-torsorial-equiv-structure-type-family-pushout :
    is-torsorial (equiv-structure-type-family-pushout s P)
  is-torsorial-equiv-structure-type-family-pushout =
    is-torsorial-Eq-structure
      ( λ PA' t eA →
        Σ ( (b : codomain-span-diagram s) →
            right-type-family-structure-type-family-pushout s P b ≃ pr1 t b)
          ( coherence-square-equiv-structure-type-family-pushout s P
            ( PA' , t)
            ( eA)))
      ( is-torsorial-Eq-Π
        ( λ a X → left-type-family-structure-type-family-pushout s P a ≃ X)
        ( λ a →
          is-torsorial-equiv
            ( left-type-family-structure-type-family-pushout s P a)))
      ( ( left-type-family-structure-type-family-pushout s  P) ,
        ( λ a → id-equiv))
      ( is-torsorial-Eq-structure
        ( λ PB' PS' eB →
          coherence-square-equiv-structure-type-family-pushout s P
            ( left-type-family-structure-type-family-pushout s P , PB' , PS')
            ( λ a → id-equiv)
            ( eB))
        ( is-torsorial-Eq-Π
          ( λ b Y → right-type-family-structure-type-family-pushout s P b ≃ Y)
          ( λ b →
            is-torsorial-equiv
              ( right-type-family-structure-type-family-pushout s P b)))
        ( ( right-type-family-structure-type-family-pushout s P) ,
          ( λ b → id-equiv))
        ( is-torsorial-Eq-Π
          ( λ x →
            htpy-equiv (matching-equiv-structure-type-family-pushout s P x))
          ( λ x →
            is-torsorial-htpy-equiv
              ( matching-equiv-structure-type-family-pushout s P x))))

  is-equiv-equiv-eq-structure-type-family-pushout :
    (Q : structure-type-family-pushout l4 s) →
    is-equiv (equiv-eq-structure-type-family-pushout Q)
  is-equiv-equiv-eq-structure-type-family-pushout =
    fundamental-theorem-id
      ( is-torsorial-equiv-structure-type-family-pushout)
      ( equiv-eq-structure-type-family-pushout)

  equiv-equiv-structure-type-family-pushout :
    (Q : structure-type-family-pushout l4 s) →
    (P ＝ Q) ≃ equiv-structure-type-family-pushout s P Q
  pr1 (equiv-equiv-structure-type-family-pushout Q) =
    equiv-eq-structure-type-family-pushout Q
  pr2 (equiv-equiv-structure-type-family-pushout Q) =
    is-equiv-equiv-eq-structure-type-family-pushout Q

  eq-equiv-structure-type-family-pushout :
    (Q : structure-type-family-pushout l4 s) →
    equiv-structure-type-family-pushout s P Q → P ＝ Q
  eq-equiv-structure-type-family-pushout Q =
    map-inv-is-equiv (is-equiv-equiv-eq-structure-type-family-pushout Q)

  is-section-eq-equiv-structure-type-family-pushout :
    (Q : structure-type-family-pushout l4 s) →
    is-section
      ( equiv-eq-structure-type-family-pushout Q)
      ( eq-equiv-structure-type-family-pushout Q)
  is-section-eq-equiv-structure-type-family-pushout Q =
    is-section-map-inv-is-equiv
      ( is-equiv-equiv-eq-structure-type-family-pushout Q)

  is-retraction-eq-equiv-structure-type-family-pushout :
    (Q : structure-type-family-pushout l4 s) →
    is-retraction
      ( equiv-eq-structure-type-family-pushout Q)
      ( eq-equiv-structure-type-family-pushout Q)
  is-retraction-eq-equiv-structure-type-family-pushout Q =
    is-retraction-map-inv-is-equiv
      ( is-equiv-equiv-eq-structure-type-family-pushout Q)
```

### Theorem 18.2.3

```agda
structure-type-family-pushout-cocone-UU :
  {l1 l2 l3 : Level} (l : Level) (s : span-diagram l1 l2 l3) →
  cocone-span-diagram s (UU l) → structure-type-family-pushout l s
structure-type-family-pushout-cocone-UU l s =
  tot (λ PA → (tot (λ PB H s → equiv-eq (H s))))

is-equiv-structure-type-family-pushout-cocone-UU :
  {l1 l2 l3 : Level} (l : Level) (s : span-diagram l1 l2 l3) →
  is-equiv (structure-type-family-pushout-cocone-UU l s)
is-equiv-structure-type-family-pushout-cocone-UU l s =
  is-equiv-tot-is-fiberwise-equiv
    ( λ PA →
      is-equiv-tot-is-fiberwise-equiv
        ( λ PB →
          is-equiv-map-Π-is-fiberwise-equiv
            ( λ x →
              univalence
                ( PA (left-map-span-diagram s x))
                ( PB (right-map-span-diagram s x)))))

htpy-equiv-eq-ap-fam :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A}
  (p : x ＝ y) → htpy-equiv (equiv-tr B p) (equiv-eq (ap B p))
htpy-equiv-eq-ap-fam B {x} {.x} refl =
  refl-htpy-equiv id-equiv

module _
  {l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X)
  where

  triangle-structure-type-family-pushout-type-family :
    coherence-triangle-maps
      ( structure-type-family-pushout-type-family {l5 = l5} s c)
      ( structure-type-family-pushout-cocone-UU l5 s)
      ( cocone-map-span-diagram s {Y = UU l5} c)
  triangle-structure-type-family-pushout-type-family P =
    eq-equiv-structure-type-family-pushout s
      ( structure-type-family-pushout-type-family s c P)
      ( structure-type-family-pushout-cocone-UU l5 s
        ( cocone-map-span-diagram s c P))
      ( pair
        ( λ a → id-equiv)
        ( pair
          ( λ b → id-equiv)
          ( λ x →
            htpy-equiv-eq-ap-fam P
              ( coherence-square-cocone-span-diagram s c x))))

  is-equiv-structure-type-family-pushout-type-family :
    universal-property-pushout s c →
    is-equiv (structure-type-family-pushout-type-family {l5 = l5} s c)
  is-equiv-structure-type-family-pushout-type-family up-c =
    is-equiv-left-map-triangle
      ( structure-type-family-pushout-type-family s c)
      ( structure-type-family-pushout-cocone-UU l5 s)
      ( cocone-map-span-diagram s c)
      ( triangle-structure-type-family-pushout-type-family)
      ( up-c (UU l5))
      ( is-equiv-structure-type-family-pushout-cocone-UU l5 s)

  equiv-structure-type-family-pushout-type-family :
    universal-property-pushout s c →
    (X → UU l5) ≃ structure-type-family-pushout l5 s
  pr1 (equiv-structure-type-family-pushout-type-family up-c) =
    structure-type-family-pushout-type-family s c
  pr2 (equiv-structure-type-family-pushout-type-family up-c) =
    is-equiv-structure-type-family-pushout-type-family up-c
```

### Corollary 18.2.4

```agda
module _
  {l1 l2 l3 l4 l : Level} (s : span-diagram l1 l2 l3) {X : UU l4} (c : cocone-span-diagram s X)
  (U : universal-property-pushout s c)
  where

  uniqueness-structure-type-family-pushout :
    (P : structure-type-family-pushout l s) →
    is-contr
      ( Σ ( X → UU l)
          ( λ Q →
            equiv-structure-type-family-pushout s P
              ( structure-type-family-pushout-type-family s c Q)))
  uniqueness-structure-type-family-pushout P =
    is-contr-equiv'
      ( fiber (structure-type-family-pushout-type-family s c) P)
      ( equiv-tot
        ( λ Q →
          ( equiv-equiv-structure-type-family-pushout s P
            ( structure-type-family-pushout-type-family s c Q)) ∘e
        ( equiv-inv (structure-type-family-pushout-type-family s c Q) P)))
      ( is-contr-map-is-equiv
        ( is-equiv-structure-type-family-pushout-type-family s c U)
        ( P))

  fam-structure-type-family-pushout :
    structure-type-family-pushout l s → X → UU l
  fam-structure-type-family-pushout P =
    pr1 (center (uniqueness-structure-type-family-pushout P))

  is-section-fam-structure-type-family-pushout :
    is-section
      ( structure-type-family-pushout-type-family {l5 = l} s c)
      ( fam-structure-type-family-pushout)
  is-section-fam-structure-type-family-pushout P =
    inv
      ( eq-equiv-structure-type-family-pushout s
      ( P)
      ( structure-type-family-pushout-type-family s c
        ( fam-structure-type-family-pushout P))
      ( pr2 (center (uniqueness-structure-type-family-pushout P))))

  compute-left-fam-structure-type-family-pushout :
    (P : structure-type-family-pushout l s) →
    (a : domain-span-diagram s) →
    pr1 P a ≃ fam-structure-type-family-pushout P (pr1 c a)
  compute-left-fam-structure-type-family-pushout P =
    pr1 (pr2 (center (uniqueness-structure-type-family-pushout P)))

  compute-right-fam-structure-type-family-pushout :
    (P : structure-type-family-pushout l s) (b : codomain-span-diagram s) →
    pr1 (pr2 P) b ≃ fam-structure-type-family-pushout P (pr1 (pr2 c) b)
  compute-right-fam-structure-type-family-pushout P =
    pr1 (pr2 (pr2 (center (uniqueness-structure-type-family-pushout P))))

  compute-path-fam-structure-type-family-pushout :
    ( P : structure-type-family-pushout l s) →
    ( x : spanning-type-span-diagram s) →
      ( ( map-equiv
          ( compute-right-fam-structure-type-family-pushout P
            ( right-map-span-diagram s x))) ∘
        ( map-equiv (pr2 (pr2 P) x))) ~
      ( ( tr
          ( fam-structure-type-family-pushout P)
          ( pr2 (pr2 c) x)) ∘
        ( map-equiv
          ( compute-left-fam-structure-type-family-pushout P
            ( left-map-span-diagram s x))))
  compute-path-fam-structure-type-family-pushout P =
    pr2 (pr2 (pr2 (center (uniqueness-structure-type-family-pushout P))))
```
