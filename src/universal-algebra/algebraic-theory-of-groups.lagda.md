# Algebraic theory of groups

```agda
module universal-algebra.algebraic-theory-of-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.groups

open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-algebraic-theories
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

There is an
{{#concept "algebraic theory of groups" Agda=algebraic-theory-Group}}. The type
of all such [algebras](universal-algebra.algebras-of-algebraic-theories.md) is
[equivalent](foundation-core.equivalences.md) to the type of
[groups](group-theory.groups.md).

## Definitions

### The algebra of groups

```agda
data group-ops : UU lzero where
  unit-group-op mul-group-op inv-group-op : group-ops

group-signature : signature lzero
pr1 group-signature = group-ops
pr2 group-signature unit-group-op = 0
pr2 group-signature mul-group-op = 2
pr2 group-signature inv-group-op = 1

data group-laws : UU lzero where
  associative-l-group-laws : group-laws
  invl-l-group-laws : group-laws
  invr-r-group-laws : group-laws
  idl-l-group-laws : group-laws
  idr-r-group-laws : group-laws

algebraic-theory-Group : Algebraic-Theory lzero group-signature
pr1 algebraic-theory-Group = group-laws
pr2 algebraic-theory-Group =
  λ where
  associative-l-group-laws →
    ( op mul-group-op
      ( ( op mul-group-op (var 0 ∷ var 1 ∷ empty-tuple)) ∷
        var 2 ∷
        empty-tuple)) ,
    ( op mul-group-op
      ( var 0 ∷ (op mul-group-op (var 1 ∷ var 2 ∷ empty-tuple)) ∷ empty-tuple))
  invl-l-group-laws →
    ( op mul-group-op
      ( op inv-group-op (var 0 ∷ empty-tuple) ∷ var 0 ∷ empty-tuple)) ,
    ( op unit-group-op empty-tuple)
  invr-r-group-laws →
    ( op mul-group-op
      ( var 0 ∷ op inv-group-op (var 0 ∷ empty-tuple) ∷ empty-tuple)) ,
    ( op unit-group-op empty-tuple)
  idl-l-group-laws →
    ( op mul-group-op (op unit-group-op empty-tuple ∷ var 0 ∷ empty-tuple)) ,
    ( var 0)
  idr-r-group-laws →
    ( op mul-group-op (var 0 ∷ op unit-group-op empty-tuple ∷ empty-tuple)) ,
    ( var 0)
    where
    op = op-term
    var = var-term

algebra-Group : (l : Level) → UU (lsuc l)
algebra-Group l = Algebra l group-signature algebraic-theory-Group
```

## Properties

### The algebra of groups is equivalent to the type of groups

```agda
group-algebra-Group :
  {l : Level} → algebra-Group l → Group l
pr1 (pr1 (group-algebra-Group ((A-Set , models-A) , satisfies-A))) = A-Set
pr1 (pr2 (pr1 (group-algebra-Group ((A-Set , models-A) , satisfies-A)))) x y =
  models-A mul-group-op (x ∷ y ∷ empty-tuple)
pr2 (pr2 (pr1 (group-algebra-Group ((A-Set , models-A) , satisfies-A)))) x y z =
  satisfies-A associative-l-group-laws
    ( λ { 0 → x ; 1 → y ; (succ-ℕ (succ-ℕ n)) → z})
pr1 (pr1 (pr2 (group-algebra-Group ((A-Set , models-A) , satisfies-A)))) =
  models-A unit-group-op empty-tuple
pr1 (pr2 (pr1 (pr2 (group-algebra-Group (_ , satisfies-A))))) x =
  satisfies-A idl-l-group-laws (λ _ → x)
pr2 (pr2 (pr1 (pr2 (group-algebra-Group (_ , satisfies-A))))) x =
  satisfies-A idr-r-group-laws (λ _ → x)
pr1 (pr2 (pr2 (group-algebra-Group ((A-Set , models-A) , satisfies-A)))) x =
  models-A inv-group-op (x ∷ empty-tuple)
pr1 (pr2 (pr2 (pr2 (group-algebra-Group (_ , satisfies-A))))) x =
  satisfies-A invl-l-group-laws (λ _ → x)
pr2 (pr2 (pr2 (pr2 (group-algebra-Group (_ , satisfies-A))))) x =
  satisfies-A invr-r-group-laws (λ _ → x)

algebra-group-Group :
  {l : Level} → Group l → algebra-Group l
algebra-group-Group G =
  pair
    ( pair
      ( set-Group G)
      ( λ where
        unit-group-op v → unit-Group G
        mul-group-op (x ∷ y ∷ empty-tuple) → mul-Group G x y
        inv-group-op (x ∷ empty-tuple) → inv-Group G x))
    ( λ where
      associative-l-group-laws assign →
        associative-mul-Group G (assign 0) (assign 1) (assign 2)
      invl-l-group-laws assign →
        left-inverse-law-mul-Group G (assign 0)
      invr-r-group-laws assign →
        right-inverse-law-mul-Group G (assign 0)
      idl-l-group-laws assign →
        left-unit-law-mul-Group G (assign 0)
      idr-r-group-laws assign →
        right-unit-law-mul-Group G (assign 0))

abstract
  equiv-group-algebra-Group :
    {l : Level} → algebra-Group l ≃ Group l
  pr1 equiv-group-algebra-Group = group-algebra-Group
  pr1 (pr1 (pr2 equiv-group-algebra-Group)) = algebra-group-Group
  pr2 (pr1 (pr2 equiv-group-algebra-Group)) G =
    eq-pair-eq-fiber
      ( eq-is-prop (is-prop-is-group-Semigroup (semigroup-Group G)))
  pr1 (pr2 (pr2 equiv-group-algebra-Group)) = algebra-group-Group
  pr2 (pr2 (pr2 equiv-group-algebra-Group)) A =
    eq-pair-Σ
      ( eq-pair-eq-fiber
        ( eq-htpy
          ( λ where
            unit-group-op → eq-htpy (λ where empty-tuple → refl)
            mul-group-op → eq-htpy (λ where (x ∷ y ∷ empty-tuple) → refl)
            inv-group-op → eq-htpy (λ where (x ∷ empty-tuple) → refl))))
      ( eq-is-prop
        ( is-prop-is-algebra
          ( group-signature) ( algebraic-theory-Group)
          ( model-Algebra group-signature algebraic-theory-Group A)))
```
