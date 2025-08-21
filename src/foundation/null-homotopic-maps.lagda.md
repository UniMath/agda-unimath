# Null-homotopic maps

```agda
module foundation.null-homotopic-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.coherently-constant-maps
open import foundation.commuting-triangles-of-identifications
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-empty-type
open import foundation.universe-levels
open import foundation.weakly-constant-maps

open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
```

</details>

## Idea

A map `f : A → B` is said to be
{{#concept "null-homotopic" Disambiguation="map of types" Agda=is-null-homotopic-map}}
if there is an element `y : B` such for every `x : A` we have `f x ＝ y`. In
other words, `f` is null-homotopic if it is
[homotopic](foundation-core.homotopies.md) to a
[constant](foundation-core.constant-maps.md) function.

## Definition

### The type of null-homotopies of a map

```agda
is-null-homotopic-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-null-homotopic-map {A = A} {B} f = Σ B (λ y → (x : A) → f x ＝ y)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-null-homotopic-map f)
  where

  center-is-null-homotopic-map : B
  center-is-null-homotopic-map = pr1 H

  contraction-is-null-homotopic-map :
    (x : A) → f x ＝ center-is-null-homotopic-map
  contraction-is-null-homotopic-map = pr2 H
```

### The type of null-homotopic maps

```agda
null-homotopic-map : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
null-homotopic-map A B = Σ (A → B) is-null-homotopic-map

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : null-homotopic-map A B)
  where

  map-null-homotopic-map : A → B
  map-null-homotopic-map = pr1 f

  is-null-homotopic-null-homotopic-map :
    is-null-homotopic-map map-null-homotopic-map
  is-null-homotopic-null-homotopic-map = pr2 f

  center-null-homotopic-map : B
  center-null-homotopic-map =
    center-is-null-homotopic-map is-null-homotopic-null-homotopic-map

  contraction-null-homotopic-map :
    (x : A) →
    map-null-homotopic-map x ＝ center-null-homotopic-map
  contraction-null-homotopic-map =
    contraction-is-null-homotopic-map is-null-homotopic-null-homotopic-map
```

## Properties

### Null-homotopic maps from `A` to `B` are in correspondence with elements of `B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  compute-null-homotopic-map : null-homotopic-map A B ≃ B
  compute-null-homotopic-map =
    equivalence-reasoning
      Σ (A → B) (is-null-homotopic-map)
      ≃ Σ B (λ b → Σ (A → B) (λ f → f ~ const A b)) by equiv-left-swap-Σ
      ≃ B by right-unit-law-Σ-is-contr (λ b → is-torsorial-htpy' (const A b))
```

### Characterizing equality of null-homotopic maps

Equality of null-homotopic maps is characterized by equality of their centers.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  Eq-null-homotopic-map : (f g : null-homotopic-map A B) → UU l2
  Eq-null-homotopic-map f g =
    center-null-homotopic-map f ＝ center-null-homotopic-map g

  refl-Eq-null-homotopic-map :
    (f : null-homotopic-map A B) → Eq-null-homotopic-map f f
  refl-Eq-null-homotopic-map f = refl

  Eq-eq-null-homotopic-map :
    (f g : null-homotopic-map A B) → f ＝ g → Eq-null-homotopic-map f g
  Eq-eq-null-homotopic-map f .f refl = refl-Eq-null-homotopic-map f

  abstract
    is-torsorial-Eq-null-homotopic-map :
      (f : null-homotopic-map A B) → is-torsorial (Eq-null-homotopic-map f)
    is-torsorial-Eq-null-homotopic-map f =
      is-contr-equiv
        ( Σ B (Id (center-null-homotopic-map f)))
        ( equiv-Σ-equiv-base
          ( Id (center-null-homotopic-map f))
          ( compute-null-homotopic-map))
        ( is-torsorial-Id (center-null-homotopic-map f))

  is-equiv-Eq-eq-null-homotopic-map :
    (f g : null-homotopic-map A B) → is-equiv (Eq-eq-null-homotopic-map f g)
  is-equiv-Eq-eq-null-homotopic-map f =
    fundamental-theorem-id
      ( is-torsorial-Eq-null-homotopic-map f)
      ( Eq-eq-null-homotopic-map f)

  extensionality-null-homotopic-map :
    (f g : null-homotopic-map A B) → (f ＝ g) ≃ Eq-null-homotopic-map f g
  extensionality-null-homotopic-map f g =
    ( Eq-eq-null-homotopic-map f g ,
      is-equiv-Eq-eq-null-homotopic-map f g)

  eq-Eq-null-homotopic-map :
    (f g : null-homotopic-map A B) → Eq-null-homotopic-map f g → f ＝ g
  eq-Eq-null-homotopic-map f g =
    map-inv-equiv (extensionality-null-homotopic-map f g)
```

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

  coherence-htpy-is-null-homotopic-map :
    (H K : is-null-homotopic-map f)
    (p : center-is-null-homotopic-map H ＝ center-is-null-homotopic-map K) →
    UU (l1 ⊔ l2)
  coherence-htpy-is-null-homotopic-map H K p =
    (x : A) →
    coherence-triangle-identifications
      ( contraction-is-null-homotopic-map K x)
      ( p)
      ( contraction-is-null-homotopic-map H x)

  htpy-is-null-homotopic-map : (H K : is-null-homotopic-map f) → UU (l1 ⊔ l2)
  htpy-is-null-homotopic-map H K =
    Σ ( center-is-null-homotopic-map H ＝ center-is-null-homotopic-map K)
      ( coherence-htpy-is-null-homotopic-map H K)

  refl-htpy-is-null-homotopic-map :
    (H : is-null-homotopic-map f) → htpy-is-null-homotopic-map H H
  refl-htpy-is-null-homotopic-map H = (refl , inv-htpy-right-unit-htpy)

  htpy-eq-is-null-homotopic-map :
    (H K : is-null-homotopic-map f) → H ＝ K → htpy-is-null-homotopic-map H K
  htpy-eq-is-null-homotopic-map H .H refl = refl-htpy-is-null-homotopic-map H

  abstract
    is-torsorial-htpy-is-null-homotopic-map :
      (H : is-null-homotopic-map f) →
      is-torsorial (htpy-is-null-homotopic-map H)
    is-torsorial-htpy-is-null-homotopic-map H =
      is-torsorial-Eq-structure
        ( is-torsorial-Id (center-is-null-homotopic-map H))
        ( center-is-null-homotopic-map H , refl)
        ( is-torsorial-htpy' (contraction-is-null-homotopic-map H ∙h refl-htpy))

  is-equiv-htpy-eq-is-null-homotopic-map :
    (H K : is-null-homotopic-map f) →
    is-equiv (htpy-eq-is-null-homotopic-map H K)
  is-equiv-htpy-eq-is-null-homotopic-map H =
    fundamental-theorem-id
      ( is-torsorial-htpy-is-null-homotopic-map H)
      ( htpy-eq-is-null-homotopic-map H)

  extensionality-is-null-homotopic-map :
    (H K : is-null-homotopic-map f) → (H ＝ K) ≃ htpy-is-null-homotopic-map H K
  extensionality-is-null-homotopic-map H K =
    ( htpy-eq-is-null-homotopic-map H K ,
      is-equiv-htpy-eq-is-null-homotopic-map H K)

  eq-htpy-is-null-homotopic-map :
    (H K : is-null-homotopic-map f) → htpy-is-null-homotopic-map H K → H ＝ K
  eq-htpy-is-null-homotopic-map H K =
    map-inv-is-equiv (is-equiv-htpy-eq-is-null-homotopic-map H K)
```

### If the domain is empty the type of null-homotopies is equivalent to elements of `B`

```agda
module _
  {l : Level} {B : UU l} {f : empty → B}
  where

  compute-is-null-homotopic-map-empty-domain : is-null-homotopic-map f ≃ B
  compute-is-null-homotopic-map-empty-domain =
    right-unit-law-Σ-is-contr
      ( λ y → dependent-universal-property-empty' (λ x → f x ＝ y))
```

### If the domain has an element then the center of the null-homotopy is unique

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  eq-center-is-null-homotopic-map-has-element-domain :
    A →
    (H K : is-null-homotopic-map f) →
    center-is-null-homotopic-map H ＝ center-is-null-homotopic-map K
  eq-center-is-null-homotopic-map-has-element-domain a H K =
    inv (contraction-is-null-homotopic-map H a) ∙
    contraction-is-null-homotopic-map K a
```

### If the codomain is a set and the domain has an element then being null-homotopic is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (is-set-B : is-set B) (a : A)
  {f : A → B}
  where

  all-elements-equal-is-null-homotopic-map-has-element-domain-is-set-codomain :
    all-elements-equal (is-null-homotopic-map f)
  all-elements-equal-is-null-homotopic-map-has-element-domain-is-set-codomain
    H K =
    eq-htpy-is-null-homotopic-map H K
      ( ( eq-center-is-null-homotopic-map-has-element-domain a H K) ,
        ( λ x → eq-is-prop (is-set-B (f x) (center-is-null-homotopic-map K))))

  is-prop-is-null-homotopic-map-has-element-domain-is-set-codomain :
    is-prop (is-null-homotopic-map f)
  is-prop-is-null-homotopic-map-has-element-domain-is-set-codomain =
    is-prop-all-elements-equal
      ( all-elements-equal-is-null-homotopic-map-has-element-domain-is-set-codomain)
```

### If the codomain is a set and the domain is inhabited then being null-homotopic is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (a : is-inhabited A) (is-set-B : is-set B)
  {f : A → B}
  where

  eq-center-is-null-homotopic-map-is-inhabited-domain-is-set-codomain :
    (H K : is-null-homotopic-map f) →
    center-is-null-homotopic-map H ＝ center-is-null-homotopic-map K
  eq-center-is-null-homotopic-map-is-inhabited-domain-is-set-codomain H K =
    rec-trunc-Prop
      ( Id-Prop
        ( B , is-set-B)
        ( center-is-null-homotopic-map H)
        ( center-is-null-homotopic-map K))
      ( λ x → eq-center-is-null-homotopic-map-has-element-domain x H K)
      ( a)

  all-elements-equal-is-null-homotopic-map-is-inhabited-domain-is-set-codomain :
    all-elements-equal (is-null-homotopic-map f)
  all-elements-equal-is-null-homotopic-map-is-inhabited-domain-is-set-codomain
    H K =
    eq-htpy-is-null-homotopic-map H K
      ( ( eq-center-is-null-homotopic-map-is-inhabited-domain-is-set-codomain
          ( H)
          ( K)) ,
        ( λ x → eq-is-prop (is-set-B (f x) (center-is-null-homotopic-map K))))

  is-prop-is-null-homotopic-map-is-inhabited-domain-is-set-codomain :
    is-prop (is-null-homotopic-map f)
  is-prop-is-null-homotopic-map-is-inhabited-domain-is-set-codomain =
    is-prop-all-elements-equal
      ( all-elements-equal-is-null-homotopic-map-is-inhabited-domain-is-set-codomain)
```

### Null-homotopic maps are constant

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-constant-map-is-null-homotopic-map :
    {f : A → B} → is-null-homotopic-map f → is-constant-map f
  is-constant-map-is-null-homotopic-map (b , H) = ((λ _ → b) , H)

  is-constant-null-homotopic-map :
    (f : null-homotopic-map A B) → is-constant-map (map-null-homotopic-map f)
  is-constant-null-homotopic-map f =
    is-constant-map-is-null-homotopic-map
      ( is-null-homotopic-null-homotopic-map f)
```

### Null-homotopic maps are weakly constant

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-weakly-constant-map-is-null-homotopic-map :
    {f : A → B} → is-null-homotopic-map f → is-weakly-constant-map f
  is-weakly-constant-map-is-null-homotopic-map (b , H) x y = H x ∙ inv (H y)

  is-weakly-constant-null-homotopic-map :
    (f : null-homotopic-map A B) →
    is-weakly-constant-map (map-null-homotopic-map f)
  is-weakly-constant-null-homotopic-map f =
    is-weakly-constant-map-is-null-homotopic-map
      ( is-null-homotopic-null-homotopic-map f)
```

## See also

- Null-homotopic maps are
  [coherently constant](foundation.coherently-constant-maps.md), and if the
  domain is pointed the two notions coincide
- [Constant pointed maps](structured-types.constant-pointed-maps.md)

## External links

- [null homotopy](https://ncatlab.org/nlab/show/null+homotopy) at $n$Lab
