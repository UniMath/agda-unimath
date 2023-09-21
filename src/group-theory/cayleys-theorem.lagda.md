# Cayley's theorem

```agda
module group-theory.cayleys-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-extensionality
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.universe-levels

open import group-theory.embeddings-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.symmetric-groups
```

</details>

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  map-Cayleys-theorem :
    type-Group G → type-Group (symmetric-Group (set-Group G))
  map-Cayleys-theorem x = equiv-mul-Group G x

  preserves-mul-map-Cayleys-theorem :
    preserves-mul-Group G (symmetric-Group (set-Group G)) map-Cayleys-theorem
  preserves-mul-map-Cayleys-theorem x y =
    eq-htpy-equiv (λ z → associative-mul-Group G x y z)

  hom-Cayleys-theorem : hom-Group G (symmetric-Group (set-Group G))
  pr1 hom-Cayleys-theorem = map-Cayleys-theorem
  pr2 hom-Cayleys-theorem = preserves-mul-map-Cayleys-theorem

  is-injective-map-Cayleys-theorem : is-injective map-Cayleys-theorem
  is-injective-map-Cayleys-theorem {x} {y} p =
    ( inv (right-unit-law-mul-Group G x)) ∙
    ( ( htpy-eq-equiv p (unit-Group G)) ∙
      ( right-unit-law-mul-Group G y))

  is-emb-map-Cayleys-theorem : is-emb map-Cayleys-theorem
  is-emb-map-Cayleys-theorem =
    is-emb-is-injective
      ( is-set-type-Group (symmetric-Group (set-Group G)))
      ( is-injective-map-Cayleys-theorem)

  Cayleys-theorem : emb-Group G (symmetric-Group (set-Group G))
  pr1 Cayleys-theorem = hom-Cayleys-theorem
  pr2 Cayleys-theorem = is-emb-map-Cayleys-theorem
```
