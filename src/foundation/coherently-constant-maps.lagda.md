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

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A map `f : A → B` is said to be
{{#concept "(coherently) constant" Disambiguation="map of types" WD="constant function "WDID=Q746264 Agda=is-constant Agda=constant-map}}
if there is a [partial element](foundation.partial-elements.md) of `B`,
`b : ║A║₋₁ → B` such that for every `x : A` we have `f x ＝ b`.
{{#cite Kraus15}}

## Definition

### The type of coherent constancies of a map

```agda
is-constant :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-constant {A = A} {B} f =
  Σ (║ A ║₋₁ → B) (λ b → (x : A) → f x ＝ b (unit-trunc-Prop x))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-constant f)
  where

  center-partial-element-is-constant : ║ A ║₋₁ → B
  center-partial-element-is-constant = pr1 H

  contraction-is-constant' :
    (x : A) → f x ＝ center-partial-element-is-constant (unit-trunc-Prop x)
  contraction-is-constant' = pr2 H

  contraction-is-constant :
    (x : A) {|x| : ║ A ║₋₁} → f x ＝ center-partial-element-is-constant |x|
  contraction-is-constant x =
    contraction-is-constant' x ∙
    ap center-partial-element-is-constant (eq-type-Prop (trunc-Prop A))
```

### The type of coherently constant maps

```agda
constant-map : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
constant-map A B = Σ (A → B) is-constant

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : constant-map A B)
  where

  map-constant-map : A → B
  map-constant-map = pr1 f

  is-constant-map-constant-map : is-constant map-constant-map
  is-constant-map-constant-map = pr2 f

  center-partial-element-constant-map : ║ A ║₋₁ → B
  center-partial-element-constant-map =
    center-partial-element-is-constant is-constant-map-constant-map

  contraction-constant-map' :
    (x : A) →
    map-constant-map x ＝ center-partial-element-constant-map (unit-trunc-Prop x)
  contraction-constant-map' =
    contraction-is-constant' is-constant-map-constant-map

  contraction-constant-map :
    (x : A) {|x| : ║ A ║₋₁} →
    map-constant-map x ＝ center-partial-element-constant-map |x|
  contraction-constant-map =
    contraction-is-constant is-constant-map-constant-map
```

## Properties

### Characterizing equality of coherent constancy witnesses

Two constancy witnesses `H` and `K` are equal if there is a homotopy
[equality](foundation-core.identity-types.md) of partial base points
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

  coherence-htpy-is-constant :
    (H K : is-constant f)
    (p :
      center-partial-element-is-constant H ~
      center-partial-element-is-constant K) →
    UU (l1 ⊔ l2)
  coherence-htpy-is-constant H K p =
    (x : A) →
    coherence-triangle-identifications
      ( contraction-is-constant' K x)
      ( p (unit-trunc-Prop x))
      ( contraction-is-constant' H x)

  htpy-is-constant : (H K : is-constant f) → UU (l1 ⊔ l2)
  htpy-is-constant H K =
    Σ ( center-partial-element-is-constant H ~
        center-partial-element-is-constant K)
      ( coherence-htpy-is-constant H K)

  refl-htpy-is-constant :
    (H : is-constant f) → htpy-is-constant H H
  refl-htpy-is-constant H = (refl-htpy , inv-htpy-right-unit-htpy)

  htpy-eq-is-constant :
    (H K : is-constant f) → H ＝ K → htpy-is-constant H K
  htpy-eq-is-constant H .H refl = refl-htpy-is-constant H

  is-torsorial-htpy-is-constant :
    (H : is-constant f) → is-torsorial (htpy-is-constant H)
  is-torsorial-htpy-is-constant H =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (center-partial-element-is-constant H))
      ( center-partial-element-is-constant H , refl-htpy)
      (is-torsorial-htpy' (contraction-is-constant' H ∙h refl-htpy))

  is-equiv-htpy-eq-is-constant :
    (H K : is-constant f) → is-equiv (htpy-eq-is-constant H K)
  is-equiv-htpy-eq-is-constant H =
    fundamental-theorem-id
      ( is-torsorial-htpy-is-constant H)
      ( htpy-eq-is-constant H)

  extensionality-htpy-is-constant :
    (H K : is-constant f) → (H ＝ K) ≃ htpy-is-constant H K
  extensionality-htpy-is-constant H K =
    ( htpy-eq-is-constant H K , is-equiv-htpy-eq-is-constant H K)

  eq-htpy-is-constant :
    (H K : is-constant f) → htpy-is-constant H K → H ＝ K
  eq-htpy-is-constant H K =
    map-inv-is-equiv (is-equiv-htpy-eq-is-constant H K)
```

### If the domain has an element then the center partial element is unique

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  eq-center-is-constant-has-element-domain :
    A → (H K : is-constant f) →
    center-partial-element-is-constant H ~ center-partial-element-is-constant K
  eq-center-is-constant-has-element-domain a H K _ =
    inv (contraction-is-constant H a) ∙ contraction-is-constant K a
```

### If the codomain is a set then being constant is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (is-set-B : is-set B)
  {f : A → B}
  where

  eq-center-is-constant-is-set-codomain :
    (H K : is-constant f) →
    center-partial-element-is-constant H ~ center-partial-element-is-constant K
  eq-center-is-constant-is-set-codomain H K |x| =
    rec-trunc-Prop
      ( Id-Prop
        ( B , is-set-B)
        ( center-partial-element-is-constant H |x|)
        ( center-partial-element-is-constant K |x|))
      ( λ x → eq-center-is-constant-has-element-domain x H K |x|)
      ( |x|)

  all-elements-equal-is-constant-is-set-codomain :
    all-elements-equal (is-constant f)
  all-elements-equal-is-constant-is-set-codomain H K =
    eq-htpy-is-constant H K
      ( ( eq-center-is-constant-is-set-codomain H K) ,
        ( λ x →
          eq-is-prop
            ( is-set-B
              ( f x)
              ( center-partial-element-is-constant K (unit-trunc-Prop x)))))

  is-prop-is-constant-is-set-codomain :
    is-prop (is-constant f)
  is-prop-is-constant-is-set-codomain =
    is-prop-all-elements-equal
      ( all-elements-equal-is-constant-is-set-codomain)
```

### Coherently constant maps from `A` to `B` are in correspondence with partial elements of `B` over `║ A ║₋₁`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  compute-constant-map : constant-map A B ≃ (║ A ║₋₁ → B)
  compute-constant-map =
    equivalence-reasoning
    Σ (A → B) (is-constant)
    ≃ Σ (║ A ║₋₁ → B) (λ b → Σ (A → B) (λ f → f ~ b ∘ unit-trunc-Prop))
    by equiv-left-swap-Σ
    ≃ (║ A ║₋₁ → B)
    by
      right-unit-law-Σ-is-contr (λ b → is-torsorial-htpy' (b ∘ unit-trunc-Prop))
```

### Coherently constant maps are weakly constant

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-weakly-constant-is-constant :
    is-constant f → is-weakly-constant f
  is-weakly-constant-is-constant H x y =
    contraction-is-constant' H x ∙ inv (contraction-is-constant H y)
```

## References

{{#bibliography}} {{#reference Kraus15}}

## See also

- [Null-homotopic maps](foundation.null-homotopic-maps.md) are coherently
  constant, and if the domain is pointed the two notions coincide.
