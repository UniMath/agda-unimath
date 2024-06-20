# Null-homotopic maps

```agda
module foundation.null-homotopic-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-identifications
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A map `f : A → B` is said to be
{{#concept "null-homotopic" Disambiguation="map of types" Agda=null-htpy}}, or
_constant_, if there is an element `y : B` such for every `x : A` we have
`f x ＝ y`. In other words, `f` is null-homotopic if it is
[homotopic](foundation-core.homotopies.md) to a
[constant](foundation-core.constant-maps.md) function.

## Definition

### The type of null-homotopies of a map

```agda
null-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
null-htpy {A = A} {B} f = Σ B (λ y → (x : A) → f x ＝ y)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : null-htpy f)
  where

  center-null-htpy : B
  center-null-htpy = pr1 H

  contraction-null-htpy : (x : A) → f x ＝ center-null-htpy
  contraction-null-htpy = pr2 H
```

## Properties

### Characterizing equality of null-homotopies

Two null-homotopies `H` and `K` are equal if there is an
[equality](foundation-core.identity-types.md) of base points `p : H₀ ＝ K₀` such
that for every `x : A` we have a
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

  coherence-htpy-null-htpy :
    (H K : null-htpy f) (p : center-null-htpy H ＝ center-null-htpy K) →
    UU (l1 ⊔ l2)
  coherence-htpy-null-htpy H K p =
    (x : A) →
    coherence-triangle-identifications
      ( contraction-null-htpy K x)
      ( p)
      ( contraction-null-htpy H x)

  htpy-null-htpy : (H K : null-htpy f) → UU (l1 ⊔ l2)
  htpy-null-htpy H K =
    Σ ( center-null-htpy H ＝ center-null-htpy K)
      ( coherence-htpy-null-htpy H K)

  refl-htpy-null-htpy : (H : null-htpy f) → htpy-null-htpy H H
  refl-htpy-null-htpy H = (refl , inv-htpy-right-unit-htpy)

  htpy-eq-null-htpy : (H K : null-htpy f) → H ＝ K → htpy-null-htpy H K
  htpy-eq-null-htpy H .H refl = refl-htpy-null-htpy H

  is-torsorial-htpy-null-htpy :
    (H : null-htpy f) → is-torsorial (htpy-null-htpy H)
  is-torsorial-htpy-null-htpy H =
    is-torsorial-Eq-structure
      ( is-torsorial-Id (center-null-htpy H))
      ( center-null-htpy H , refl)
      ( is-torsorial-htpy' (contraction-null-htpy H ∙h refl-htpy))

  is-equiv-htpy-eq-null-htpy :
    (H K : null-htpy f) → is-equiv (htpy-eq-null-htpy H K)
  is-equiv-htpy-eq-null-htpy H =
    fundamental-theorem-id (is-torsorial-htpy-null-htpy H) (htpy-eq-null-htpy H)

  extensionality-htpy-null-htpy :
    (H K : null-htpy f) → (H ＝ K) ≃ htpy-null-htpy H K
  extensionality-htpy-null-htpy H K =
    ( htpy-eq-null-htpy H K , is-equiv-htpy-eq-null-htpy H K)

  eq-htpy-null-htpy : (H K : null-htpy f) → htpy-null-htpy H K → H ＝ K
  eq-htpy-null-htpy H K = map-inv-is-equiv (is-equiv-htpy-eq-null-htpy H K)
```

### If the domain is empty the type of null-homotopies is equivalent to elements of `B`

```agda
module _
  {l : Level} {B : UU l} {f : empty → B}
  where

  compute-null-htpy-empty-domain : null-htpy f ≃ B
  compute-null-htpy-empty-domain =
    right-unit-law-Σ-is-contr
      ( λ y → dependent-universal-property-empty' (λ x → f x ＝ y))
```

### If the domain has an element then the center of the null-homotopy is unique

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  eq-center-null-htpy-has-element-domain :
    A → (H K : null-htpy f) → center-null-htpy H ＝ center-null-htpy K
  eq-center-null-htpy-has-element-domain a H K =
    inv (contraction-null-htpy H a) ∙ contraction-null-htpy K a
```

### If the codomain is a set and the domain has an element then being null-homotopic is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (is-set-B : is-set B) (a : A)
  {f : A → B}
  where

  all-elements-equal-null-htpy-has-element-domain-is-set-codomain :
    all-elements-equal (null-htpy f)
  all-elements-equal-null-htpy-has-element-domain-is-set-codomain H K =
    eq-htpy-null-htpy H K
      ( ( eq-center-null-htpy-has-element-domain a H K) ,
        ( λ x → eq-is-prop (is-set-B (f x) (center-null-htpy K))))

  is-prop-null-htpy-has-element-domain-is-set-codomain : is-prop (null-htpy f)
  is-prop-null-htpy-has-element-domain-is-set-codomain =
    is-prop-all-elements-equal
      ( all-elements-equal-null-htpy-has-element-domain-is-set-codomain)
```

### If the codomain is a set and the domain is inhabited then being null-homotopic is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (a : is-inhabited A) (is-set-B : is-set B)
  {f : A → B}
  where

  eq-center-null-htpy-is-inhabited-domain-is-set-codomain :
    (H K : null-htpy f) → center-null-htpy H ＝ center-null-htpy K
  eq-center-null-htpy-is-inhabited-domain-is-set-codomain H K =
    rec-trunc-Prop
      ( Id-Prop (B , is-set-B) (center-null-htpy H) (center-null-htpy K))
      ( λ x → eq-center-null-htpy-has-element-domain x H K)
      ( a)

  all-elements-equal-null-htpy-is-inhabited-domain-is-set-codomain :
    all-elements-equal (null-htpy f)
  all-elements-equal-null-htpy-is-inhabited-domain-is-set-codomain H K =
    eq-htpy-null-htpy H K
      ( ( eq-center-null-htpy-is-inhabited-domain-is-set-codomain H K) ,
        ( λ x → eq-is-prop (is-set-B (f x) (center-null-htpy K))))

  is-prop-null-htpy-is-inhabited-domain-is-set-codomain : is-prop (null-htpy f)
  is-prop-null-htpy-is-inhabited-domain-is-set-codomain =
    is-prop-all-elements-equal
      ( all-elements-equal-null-htpy-is-inhabited-domain-is-set-codomain)
```

### Null-homotopic maps from `A` to `B` are in correspondence with elements of `B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  compute-null-homotopic-map : Σ (A → B) (null-htpy) ≃ B
  compute-null-homotopic-map =
    equivalence-reasoning
      Σ (A → B) (null-htpy)
      ≃ Σ B (λ b → Σ (A → B) (λ f → f ~ const A b)) by equiv-left-swap-Σ
      ≃ B by right-unit-law-Σ-is-contr (λ b → is-torsorial-htpy' (const A b))
```

## See also

- [Weakly constant maps](foundation.weakly-constant-maps.md)
