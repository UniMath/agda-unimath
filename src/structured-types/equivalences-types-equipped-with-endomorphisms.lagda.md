# Equivalences of types equipped with endomorphisms

```agda
module structured-types.equivalences-types-equipped-with-endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import structured-types.morphisms-types-equipped-with-endomorphisms
open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Definition

### Equivalences of types equipped with endomorphisms

```agda
module _
  {l1 l2 : Level} (X : Endo l1) (Y : Endo l2)
  where

  equiv-Endo : UU (l1 ⊔ l2)
  equiv-Endo =
    Σ ( type-Endo X ≃ type-Endo Y)
      ( λ e →
        coherence-square-maps
          ( map-equiv e)
          ( endomorphism-Endo X)
          ( endomorphism-Endo Y)
          ( map-equiv e))

  equiv-equiv-Endo : equiv-Endo → type-Endo X ≃ type-Endo Y
  equiv-equiv-Endo e = pr1 e

  map-equiv-Endo : equiv-Endo → type-Endo X → type-Endo Y
  map-equiv-Endo e = map-equiv (equiv-equiv-Endo e)

  coherence-square-equiv-Endo :
    (e : equiv-Endo) →
    coherence-square-maps
      ( map-equiv-Endo e)
      ( endomorphism-Endo X)
      ( endomorphism-Endo Y)
      ( map-equiv-Endo e)
  coherence-square-equiv-Endo e = pr2 e
```

### The identity equivalence

```agda
module _
  {l1 : Level} (X : Endo l1)
  where

  id-equiv-Endo : equiv-Endo X X
  pr1 id-equiv-Endo = id-equiv
  pr2 id-equiv-Endo = refl-htpy
```

### Composition for equivalences of types equipped with endomorphisms

```agda
comp-equiv-Endo :
  {l1 l2 l3 : Level} (X : Endo l1) (Y : Endo l2) (Z : Endo l3) →
  equiv-Endo Y Z → equiv-Endo X Y → equiv-Endo X Z
pr1 (comp-equiv-Endo X Y Z f e) = pr1 f ∘e pr1 e
pr2 (comp-equiv-Endo X Y Z f e) =
  pasting-horizontal-coherence-square-maps
    ( map-equiv-Endo X Y e)
    ( map-equiv-Endo Y Z f)
    ( endomorphism-Endo X)
    ( endomorphism-Endo Y)
    ( endomorphism-Endo Z)
    ( map-equiv-Endo X Y e)
    ( map-equiv-Endo Y Z f)
    ( coherence-square-equiv-Endo X Y e)
    ( coherence-square-equiv-Endo Y Z f)
```

### Inverses of equivalences of types equipped with endomorphisms

```agda
inv-equiv-Endo :
  {l1 l2 : Level} (X : Endo l1) (Y : Endo l2) → equiv-Endo X Y → equiv-Endo Y X
pr1 (inv-equiv-Endo X Y e) = inv-equiv (equiv-equiv-Endo X Y e)
pr2 (inv-equiv-Endo X Y e) =
  coherence-square-inv-horizontal
    ( equiv-equiv-Endo X Y e)
    ( endomorphism-Endo X)
    ( endomorphism-Endo Y)
    ( equiv-equiv-Endo X Y e)
    ( coherence-square-equiv-Endo X Y e)
```

### Homotopies of equivalences of types equipped with endomorphisms

```agda
module _
  {l1 l2 : Level} (X : Endo l1) (Y : Endo l2)
  where

  hom-equiv-Endo : equiv-Endo X Y → hom-Endo X Y
  pr1 (hom-equiv-Endo e) = map-equiv-Endo X Y e
  pr2 (hom-equiv-Endo e) = coherence-square-equiv-Endo X Y e

  htpy-equiv-Endo : (e f : equiv-Endo X Y) → UU (l1 ⊔ l2)
  htpy-equiv-Endo e f = htpy-hom-Endo X Y (hom-equiv-Endo e) (hom-equiv-Endo f)

  refl-htpy-equiv-Endo : (e : equiv-Endo X Y) → htpy-equiv-Endo e e
  refl-htpy-equiv-Endo e = refl-htpy-hom-Endo X Y (hom-equiv-Endo e)

  htpy-eq-equiv-Endo : (e f : equiv-Endo X Y) → Id e f → htpy-equiv-Endo e f
  htpy-eq-equiv-Endo e .e refl = refl-htpy-equiv-Endo e

  is-contr-total-htpy-equiv-Endo :
    (e : equiv-Endo X Y) → is-contr (Σ (equiv-Endo X Y) (htpy-equiv-Endo e))
  is-contr-total-htpy-equiv-Endo e =
    is-contr-equiv
      ( Σ ( Σ (hom-Endo X Y) (λ f → is-equiv (map-hom-Endo X Y f)))
          ( λ f → htpy-hom-Endo X Y (hom-equiv-Endo e) (pr1 f)))
      ( equiv-Σ
        ( λ f → htpy-hom-Endo X Y (hom-equiv-Endo e) (pr1 f))
        ( equiv-right-swap-Σ)
        ( λ f → id-equiv))
      ( is-contr-total-Eq-subtype
        ( is-contr-total-htpy-hom-Endo X Y (hom-equiv-Endo e))
        ( λ f → is-property-is-equiv (pr1 f))
        ( hom-equiv-Endo e)
        ( refl-htpy-hom-Endo X Y (hom-equiv-Endo e))
        ( pr2 (pr1 e)))

  is-equiv-htpy-eq-equiv-Endo :
    (e f : equiv-Endo X Y) → is-equiv (htpy-eq-equiv-Endo e f)
  is-equiv-htpy-eq-equiv-Endo e =
    fundamental-theorem-id
      ( is-contr-total-htpy-equiv-Endo e)
      ( htpy-eq-equiv-Endo e)

  extensionality-equiv-Endo :
    (e f : equiv-Endo X Y) → Id e f ≃ htpy-equiv-Endo e f
  pr1 (extensionality-equiv-Endo e f) = htpy-eq-equiv-Endo e f
  pr2 (extensionality-equiv-Endo e f) = is-equiv-htpy-eq-equiv-Endo e f

  eq-htpy-equiv-Endo : (e f : equiv-Endo X Y) → htpy-equiv-Endo e f → Id e f
  eq-htpy-equiv-Endo e f =
    map-inv-equiv (extensionality-equiv-Endo e f)
```

## Properties

### Unit laws for composition of equivalences of types equipped with endomorphisms

```agda
module _
  {l1 l2 : Level} (X : Endo l1) (Y : Endo l2)
  where

  left-unit-law-comp-equiv-Endo :
    (e : equiv-Endo X Y) → Id (comp-equiv-Endo X Y Y (id-equiv-Endo Y) e) e
  left-unit-law-comp-equiv-Endo e =
    eq-htpy-equiv-Endo X Y
      ( comp-equiv-Endo X Y Y (id-equiv-Endo Y) e)
      ( e)
      ( pair
        ( refl-htpy)
        ( λ x →
          inv
            ( ( right-unit) ∙
              ( right-unit ∙ ap-id (coherence-square-equiv-Endo X Y e x)))))

  right-unit-law-comp-equiv-Endo :
    (e : equiv-Endo X Y) → Id (comp-equiv-Endo X X Y e (id-equiv-Endo X)) e
  right-unit-law-comp-equiv-Endo e =
    eq-htpy-equiv-Endo X Y
      ( comp-equiv-Endo X X Y e (id-equiv-Endo X))
      ( e)
      ( pair
        ( refl-htpy)
        ( λ x → inv right-unit))
```

### Univalence for types equipped with endomorphisms

```agda
module _
  {l1 : Level} (X : Endo l1)
  where

  equiv-eq-Endo : (Y : Endo l1) → Id X Y → equiv-Endo X Y
  equiv-eq-Endo .X refl = id-equiv-Endo X

  is-contr-total-equiv-Endo : is-contr (Σ (Endo l1) (equiv-Endo X))
  is-contr-total-equiv-Endo =
    is-contr-total-Eq-structure
      ( λ Y f e → (map-equiv e ∘ endomorphism-Endo X) ~ (f ∘ map-equiv e))
      ( is-contr-total-equiv (type-Endo X))
      ( pair (type-Endo X) id-equiv)
      ( is-contr-total-htpy (endomorphism-Endo X))

  is-equiv-equiv-eq-Endo : (Y : Endo l1) → is-equiv (equiv-eq-Endo Y)
  is-equiv-equiv-eq-Endo =
    fundamental-theorem-id
      is-contr-total-equiv-Endo
      equiv-eq-Endo

  eq-equiv-Endo : (Y : Endo l1) → equiv-Endo X Y → Id X Y
  eq-equiv-Endo Y = map-inv-is-equiv (is-equiv-equiv-eq-Endo Y)

module _
  {l : Level} (X : Endo l) (Y : Endo l) (Z : Endo l)
  where

  preserves-concat-equiv-eq-Endo :
    (p : Id X Y) (q : Id Y Z) →
    Id
      ( equiv-eq-Endo X Z (p ∙ q))
      ( comp-equiv-Endo X Y Z (equiv-eq-Endo Y Z q) (equiv-eq-Endo X Y p))
  preserves-concat-equiv-eq-Endo refl q =
    inv (right-unit-law-comp-equiv-Endo X Z (equiv-eq-Endo X Z q))
```
