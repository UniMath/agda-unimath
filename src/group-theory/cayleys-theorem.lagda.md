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
open import foundation.sets
open import foundation.universe-levels

open import group-theory.embeddings-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.symmetric-groups
```

</details>

## Idea

{{#concept "Cayley's theorem" Disambiguation="for abstract groups" WD="Cayley's theorem" WDID=Q179208 Agda=Cayleys-theorem}}
states that every [group](group-theory.groups.md) is a
[subgroup](group-theory.subgroups.md) of a
[symmetric group](group-theory.symmetric-groups.md).

## Theorem

### Direct proof of Cayley's theorem

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  map-Cayleys-theorem :
    type-Group G → type-Group (symmetric-Group (set-Group G))
  map-Cayleys-theorem = equiv-mul-Group G

  preserves-mul-map-Cayleys-theorem :
    preserves-mul-Group G (symmetric-Group (set-Group G)) map-Cayleys-theorem
  preserves-mul-map-Cayleys-theorem {x} {y} =
    eq-htpy-equiv (associative-mul-Group G x y)

  hom-Cayleys-theorem : hom-Group G (symmetric-Group (set-Group G))
  pr1 hom-Cayleys-theorem = map-Cayleys-theorem
  pr2 hom-Cayleys-theorem = preserves-mul-map-Cayleys-theorem

  is-injective-map-Cayleys-theorem : is-injective map-Cayleys-theorem
  is-injective-map-Cayleys-theorem {x} {y} p =
    ( inv (right-unit-law-mul-Group G x)) ∙
    ( htpy-eq-equiv p (unit-Group G)) ∙
    ( right-unit-law-mul-Group G y)

  is-emb-map-Cayleys-theorem : is-emb map-Cayleys-theorem
  is-emb-map-Cayleys-theorem =
    is-emb-is-injective
      ( is-set-type-Group (symmetric-Group (set-Group G)))
      ( is-injective-map-Cayleys-theorem)

  Cayleys-theorem : emb-Group G (symmetric-Group (set-Group G))
  pr1 Cayleys-theorem = hom-Cayleys-theorem
  pr2 Cayleys-theorem = is-emb-map-Cayleys-theorem
```

### Cayley's theorem as a corollary of the Yoneda lemma

This is Corollary 2.2.10 of {{#cite Rie17}}, and remains to be formalized.

## References

{{#bibliography}}

## External links

- [Cayley's Theorem](https://1lab.dev/Algebra.Group.Cayley.html) at 1lab
- [Cayley's theorem](https://ncatlab.org/nlab/show/Cayley%27s+theorem) at $n$Lab
- [Cayley's theorem](https://en.wikipedia.org/wiki/Cayley%27s_theorem) at
  Wikipedia
- [Cayley's theorem](https://www.wikidata.org/wiki/Q179208) at Wikidata
