# Semisimple commutative finite rings

```agda
module univalent-combinatorics.semisimple-commutative-finite-rings where
```

<details><summary>Imports</summary>

```agda
open import univalent-combinatorics.commutative-finite-rings
open import univalent-combinatorics.finite-types

open import univalent-combinatorics.finite-fields
open import univalent-combinatorics.homomorphisms-commutative-finite-rings
open import univalent-combinatorics.dependent-products-commutative-finite-rings

open import commutative-algebra.commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.involutions
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.unital-binary-operations
open import foundation.universe-levels
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.functions

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import lists.concatenation-lists
open import lists.lists

open import ring-theory.rings
open import ring-theory.semirings

open import ring-theory.division-rings
```

</details>

## Idea

A **semisimple commutative finite rings** is a commutative finie rings wich is merely equivalent to an iterated cartesian product of finite fields.

## Definitions

### Semisimple commutative finite rings

```agda
is-semisimple-Commutative-Ring-𝔽 :
  {l1 : Level} (l2 l3 : Level) → Commutative-Ring-𝔽 l1 →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
is-semisimple-Commutative-Ring-𝔽 l2 l3 R =
  exists
    ( 𝔽 l2)
    ( λ I →
      exists-Prop
        ( type-𝔽 I → Field-𝔽 l3)
        ( λ A →
          trunc-Prop
            ( type-hom-Commutative-Ring-𝔽
              ( R)
              ( Π-Commutative-Ring-𝔽
                ( I)
                ( commutative-finite-ring-Field-𝔽 ∘ A)))))

Semisimple-Commutative-Ring-𝔽 :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Semisimple-Commutative-Ring-𝔽 l1 l2 l3 =
  Σ (Commutative-Ring-𝔽 l1) (is-semisimple-Commutative-Ring-𝔽 l2 l3)
```

### Equip a finite type with a structure of semisimple commutative finite ring

```agda
structure-semisimple-commutative-ring-𝔽 :
  {l1 : Level} (l2 l3 : Level) → 𝔽 l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
structure-semisimple-commutative-ring-𝔽 l2 l3 X =
  Σ ( structure-commutative-ring-𝔽 X)
    ( λ r →
      is-semisimple-Commutative-Ring-𝔽
        ( l2)
        ( l3)
        ( compute-structure-commutative-ring-𝔽 X r))

compute-structure-semisimple-commutative-ring-𝔽 :
  {l1 : Level} (l2 l3 : Level) → (X : 𝔽 l1) →
  structure-semisimple-commutative-ring-𝔽 l2 l3 X →
  Semisimple-Commutative-Ring-𝔽 l1 l2 l3
pr1 (compute-structure-semisimple-commutative-ring-𝔽 l2 l3 X (p , s)) =
  compute-structure-commutative-ring-𝔽 X p
pr2 (compute-structure-semisimple-commutative-ring-𝔽 l2 l3 X (p , s)) = s
```
