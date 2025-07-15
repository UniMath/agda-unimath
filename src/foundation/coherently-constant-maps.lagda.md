# Coherently constant maps

```agda
module foundation.coherently-constant-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-identifications
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.weakly-constant-maps

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
```

</details>

## Idea

A map `f : A → B` is said to be
{{#concept "(coherently) constant" Disambiguation="map of types" WD="constant function" WDID=Q746264 Agda=is-constant-map Agda=constant-map}}
if there is a [partial element](foundation.partial-elements.md) of `B`,
`b : ║A║₋₁ → B` such that for every `x : A` we have `f x ＝ b`.
{{#cite Kraus15}}

## Definition

### The type of constancy witnesses of a map

```agda
is-constant-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-constant-map {A = A} {B} f =
  Σ (║ A ║₋₁ → B) (λ b → (x : A) → f x ＝ b (unit-trunc-Prop x))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-constant-map f)
  where

  center-partial-element-is-constant-map : ║ A ║₋₁ → B
  center-partial-element-is-constant-map = pr1 H

  contraction-is-constant-map' :
    (x : A) → f x ＝ center-partial-element-is-constant-map (unit-trunc-Prop x)
  contraction-is-constant-map' = pr2 H

  contraction-is-constant-map :
    (x : A) {|x| : ║ A ║₋₁} → f x ＝ center-partial-element-is-constant-map |x|
  contraction-is-constant-map x =
    contraction-is-constant-map' x ∙
    ap center-partial-element-is-constant-map (eq-type-Prop (trunc-Prop A))
```

### The type of coherently constant maps

```agda
constant-map : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
constant-map A B = Σ (A → B) is-constant-map

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : constant-map A B)
  where

  map-constant-map : A → B
  map-constant-map = pr1 f

  is-constant-constant-map : is-constant-map map-constant-map
  is-constant-constant-map = pr2 f

  center-partial-element-constant-map : ║ A ║₋₁ → B
  center-partial-element-constant-map =
    center-partial-element-is-constant-map is-constant-constant-map

  contraction-constant-map' :
    (x : A) →
    map-constant-map x ＝ center-partial-element-constant-map (unit-trunc-Prop x)
  contraction-constant-map' =
    contraction-is-constant-map' is-constant-constant-map

  contraction-constant-map :
    (x : A) {|x| : ║ A ║₋₁} →
    map-constant-map x ＝ center-partial-element-constant-map |x|
  contraction-constant-map =
    contraction-is-constant-map is-constant-constant-map
```

## Properties

### Coherently constant maps from `A` to `B` are in correspondence with partial elements of `B` over `║ A ║₋₁`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  compute-constant-map : constant-map A B ≃ (║ A ║₋₁ → B)
  compute-constant-map =
    equivalence-reasoning
    Σ (A → B) (is-constant-map)
    ≃ Σ (║ A ║₋₁ → B) (λ b → Σ (A → B) (λ f → f ~ b ∘ unit-trunc-Prop))
    by equiv-left-swap-Σ
    ≃ (║ A ║₋₁ → B)
    by
      right-unit-law-Σ-is-contr (λ b → is-torsorial-htpy' (b ∘ unit-trunc-Prop))
```

### Characterizing equality of coherently constant maps

Equality of constant maps is characterized by homotopy of their centers.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  htpy-constant-map : (f g : constant-map A B) → UU (l1 ⊔ l2)
  htpy-constant-map f g =
    center-partial-element-constant-map f ~
    center-partial-element-constant-map g

  refl-htpy-constant-map :
    (f : constant-map A B) → htpy-constant-map f f
  refl-htpy-constant-map f = refl-htpy

  htpy-eq-constant-map :
    (f g : constant-map A B) → f ＝ g → htpy-constant-map f g
  htpy-eq-constant-map f .f refl = refl-htpy-constant-map f

  abstract
    is-torsorial-htpy-constant-map :
      (f : constant-map A B) → is-torsorial (htpy-constant-map f)
    is-torsorial-htpy-constant-map f =
      is-contr-equiv
        ( Σ (║ A ║₋₁ → B) (center-partial-element-constant-map f ~_))
        ( equiv-Σ-equiv-base
          ( center-partial-element-constant-map f ~_)
          ( compute-constant-map))
        ( is-torsorial-htpy (center-partial-element-constant-map f))

  is-equiv-htpy-eq-constant-map :
    (f g : constant-map A B) → is-equiv (htpy-eq-constant-map f g)
  is-equiv-htpy-eq-constant-map f =
    fundamental-theorem-id
      ( is-torsorial-htpy-constant-map f)
      ( htpy-eq-constant-map f)

  extensionality-constant-map :
    (f g : constant-map A B) → (f ＝ g) ≃ htpy-constant-map f g
  extensionality-constant-map f g =
    ( htpy-eq-constant-map f g ,
      is-equiv-htpy-eq-constant-map f g)

  eq-htpy-constant-map :
    (f g : constant-map A B) → htpy-constant-map f g → f ＝ g
  eq-htpy-constant-map f g =
    map-inv-equiv (extensionality-constant-map f g)
```

### Characterizing equality of constancy witnesses

Two constancy witnesses `H` and `K` are equal if there is a homotopy of centers
`p : H₀ ~ K₀` such that for every `x : A` we have a
[commuting triangle of identifications](foundation.commuting-triangles-of-identifications.md)

```text
        f x
        / \
   H₁x /   \ K₁x
      ∨     ∨
    H₀ ----> K₀.
         p
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  coherence-htpy-is-constant-map :
    (H K : is-constant-map f)
    (p :
      center-partial-element-is-constant-map H ~
      center-partial-element-is-constant-map K) →
    UU (l1 ⊔ l2)
  coherence-htpy-is-constant-map H K p =
    (x : A) →
    coherence-triangle-identifications
      ( contraction-is-constant-map' K x)
      ( p (unit-trunc-Prop x))
      ( contraction-is-constant-map' H x)

  htpy-is-constant-map : (H K : is-constant-map f) → UU (l1 ⊔ l2)
  htpy-is-constant-map H K =
    Σ ( center-partial-element-is-constant-map H ~
        center-partial-element-is-constant-map K)
      ( coherence-htpy-is-constant-map H K)

  refl-htpy-is-constant-map :
    (H : is-constant-map f) → htpy-is-constant-map H H
  refl-htpy-is-constant-map H = (refl-htpy , inv-htpy-right-unit-htpy)

  htpy-eq-is-constant-map :
    (H K : is-constant-map f) → H ＝ K → htpy-is-constant-map H K
  htpy-eq-is-constant-map H .H refl = refl-htpy-is-constant-map H

  abstract
    is-torsorial-htpy-is-constant-map :
      (H : is-constant-map f) → is-torsorial (htpy-is-constant-map H)
    is-torsorial-htpy-is-constant-map H =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (center-partial-element-is-constant-map H))
        ( center-partial-element-is-constant-map H , refl-htpy)
        ( is-torsorial-htpy' (contraction-is-constant-map' H ∙h refl-htpy))

  is-equiv-htpy-eq-is-constant-map :
    (H K : is-constant-map f) → is-equiv (htpy-eq-is-constant-map H K)
  is-equiv-htpy-eq-is-constant-map H =
    fundamental-theorem-id
      ( is-torsorial-htpy-is-constant-map H)
      ( htpy-eq-is-constant-map H)

  extensionality-is-constant-map :
    (H K : is-constant-map f) → (H ＝ K) ≃ htpy-is-constant-map H K
  extensionality-is-constant-map H K =
    ( htpy-eq-is-constant-map H K , is-equiv-htpy-eq-is-constant-map H K)

  eq-htpy-is-constant-map :
    (H K : is-constant-map f) → htpy-is-constant-map H K → H ＝ K
  eq-htpy-is-constant-map H K =
    map-inv-is-equiv (is-equiv-htpy-eq-is-constant-map H K)
```

### If the domain has an element then the center partial element is unique

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  htpy-center-is-constant-map-has-element-domain :
    A → (H K : is-constant-map f) →
    center-partial-element-is-constant-map H ~
    center-partial-element-is-constant-map K
  htpy-center-is-constant-map-has-element-domain a H K _ =
    inv (contraction-is-constant-map H a) ∙ contraction-is-constant-map K a
```

### If the codomain is a set then being constant is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (is-set-B : is-set B)
  {f : A → B}
  where

  htpy-center-is-constant-map-is-set-codomain :
    (H K : is-constant-map f) →
    center-partial-element-is-constant-map H ~
    center-partial-element-is-constant-map K
  htpy-center-is-constant-map-is-set-codomain H K |x| =
    rec-trunc-Prop
      ( Id-Prop
        ( B , is-set-B)
        ( center-partial-element-is-constant-map H |x|)
        ( center-partial-element-is-constant-map K |x|))
      ( λ x → htpy-center-is-constant-map-has-element-domain x H K |x|)
      ( |x|)

  all-elements-equal-is-constant-map-is-set-codomain :
    all-elements-equal (is-constant-map f)
  all-elements-equal-is-constant-map-is-set-codomain H K =
    eq-htpy-is-constant-map H K
      ( ( htpy-center-is-constant-map-is-set-codomain H K) ,
        ( λ x →
          eq-is-prop
            ( is-set-B
              ( f x)
              ( center-partial-element-is-constant-map K (unit-trunc-Prop x)))))

  is-prop-is-constant-map-is-set-codomain : is-prop (is-constant-map f)
  is-prop-is-constant-map-is-set-codomain =
    is-prop-all-elements-equal
      ( all-elements-equal-is-constant-map-is-set-codomain)
```

### Coherently constant maps are weakly constant

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-weakly-constant-map-is-constant-map :
    {f : A → B} → is-constant-map f → is-weakly-constant-map f
  is-weakly-constant-map-is-constant-map H x y =
    contraction-is-constant-map' H x ∙ inv (contraction-is-constant-map H y)

  is-weakly-constant-constant-map :
    (f : constant-map A B) → is-weakly-constant-map (map-constant-map f)
  is-weakly-constant-constant-map f =
    is-weakly-constant-map-is-constant-map (is-constant-constant-map f)
```

## References

{{#bibliography}} {{#reference Kraus15}}

## See also

- [Null-homotopic maps](foundation.null-homotopic-maps.md) are coherently
  constant, and if the domain is pointed the two notions coincide.
