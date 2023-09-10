# Functoriality of the loop space operation

```agda
module synthetic-homotopy-theory.functoriality-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.faithful-maps
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.faithful-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

Any pointed map `f : A →∗ B` induces a map `map-Ω f : Ω A →∗ Ω B`. Furthermore,
this operation respects the groupoidal operations on loop spaces.

## Definition

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  map-Ω : type-Ω A → type-Ω B
  map-Ω p =
    tr-type-Ω
      ( preserves-point-pointed-map f)
      ( ap (map-pointed-map f) p)

  preserves-refl-map-Ω : Id (map-Ω refl) refl
  preserves-refl-map-Ω = preserves-refl-tr-Ω (pr2 f)

  pointed-map-Ω : Ω A →∗ Ω B
  pointed-map-Ω = pair map-Ω preserves-refl-map-Ω

  preserves-mul-map-Ω :
    (x y : type-Ω A) → Id (map-Ω (mul-Ω A x y)) (mul-Ω B (map-Ω x) (map-Ω y))
  preserves-mul-map-Ω x y =
    ( ap
      ( tr-type-Ω (preserves-point-pointed-map f))
      ( ap-concat (map-pointed-map f) x y)) ∙
    ( preserves-mul-tr-Ω
      ( preserves-point-pointed-map f)
      ( ap (map-pointed-map f) x)
      ( ap (map-pointed-map f) y))

  preserves-inv-map-Ω :
    (x : type-Ω A) → Id (map-Ω (inv-Ω A x)) (inv-Ω B (map-Ω x))
  preserves-inv-map-Ω x =
    ( ap
      ( tr-type-Ω (preserves-point-pointed-map f))
      ( ap-inv (map-pointed-map f) x)) ∙
    ( preserves-inv-tr-Ω
      ( preserves-point-pointed-map f)
      ( ap (map-pointed-map f) x))
```

### Faithful pointed maps induce embeddings on loop spaces

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  is-emb-map-Ω :
    (f : A →∗ B) → is-faithful (map-pointed-map f) → is-emb (map-Ω f)
  is-emb-map-Ω f H =
    is-emb-comp
      ( tr-type-Ω (preserves-point-pointed-map f))
      ( ap (map-pointed-map f))
      ( is-emb-is-equiv
        ( is-equiv-tr-type-Ω (preserves-point-pointed-map f)))
      ( H (point-Pointed-Type A) (point-Pointed-Type A))

  emb-Ω :
    faithful-pointed-map A B → type-Ω A ↪ type-Ω B
  pr1 (emb-Ω f) = map-Ω (pointed-map-faithful-pointed-map f)
  pr2 (emb-Ω f) =
    is-emb-map-Ω
      ( pointed-map-faithful-pointed-map f)
      ( is-faithful-faithful-pointed-map f)
```

### Pointed embeddings induce pointed equivalences on loop spaces

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B) (t : is-emb (map-pointed-map f))
  where

  is-equiv-map-Ω-emb :
    is-equiv (map-Ω f)
  is-equiv-map-Ω-emb =
    is-equiv-comp
      ( tr-type-Ω (preserves-point-pointed-map f))
      ( ap (map-pointed-map f))
      ( t (point-Pointed-Type A) (point-Pointed-Type A))
      ( is-equiv-tr-type-Ω (preserves-point-pointed-map f))

  equiv-map-Ω-emb :
    type-Ω A ≃ type-Ω B
  pr1 equiv-map-Ω-emb = map-Ω f
  pr2 equiv-map-Ω-emb = is-equiv-map-Ω-emb

  pointed-equiv-pointed-map-Ω-emb :
    Ω A ≃∗ Ω B
  pr1 pointed-equiv-pointed-map-Ω-emb = equiv-map-Ω-emb
  pr2 pointed-equiv-pointed-map-Ω-emb = preserves-refl-map-Ω f
```

### the operator `pointed-map-Ω` preserves equivalences

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (e : A ≃∗ B)
  where

  equiv-map-Ω-pointed-equiv :
    type-Ω A ≃ type-Ω B
  equiv-map-Ω-pointed-equiv =
    equiv-map-Ω-emb
      ( pointed-map-pointed-equiv e)
      ( is-emb-is-equiv (is-equiv-map-equiv-pointed-equiv e))
```

### `pointed-map-Ω` preserves pointed equivalences

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (e : A ≃∗ B)
  where

  pointed-equiv-Ω-pointed-equiv :
    Ω A ≃∗ Ω B
  pr1 pointed-equiv-Ω-pointed-equiv = equiv-map-Ω-pointed-equiv e
  pr2 pointed-equiv-Ω-pointed-equiv =
    preserves-refl-map-Ω (pointed-map-pointed-equiv e)
```
