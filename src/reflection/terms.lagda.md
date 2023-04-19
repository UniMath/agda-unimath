# Terms

```agda
module reflection.terms where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import lists.lists
open import foundation-core.dependent-pair-types
open import foundation.cartesian-product-types
open import foundation.booleans
open import foundation.universe-levels
open import foundation.strings
open import foundation.characters
open import foundation.floats
open import foundation.machine-integers
open import foundation.unit-type
open import foundation.identity-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.addition-integers

open import reflection.names
open import reflection.arguments
open import reflection.metavariables
open import reflection.literals
open import reflection.abstractions
```

</details>

## Idea

-- TODO

## Definition

```agda
data Term    : UU lzero
data Sort    : UU lzero
data Pattern : UU lzero
data Clause  : UU lzero
Telescope = list (String × Arg Term)

data Term where
  var       : (x : ℕ) (args : list (Arg Term)) → Term
  con       : (c : Name) (args : list (Arg Term)) → Term
  def       : (f : Name) (args : list (Arg Term)) → Term
  lam       : (v : Visibility) (t : Abs Term) → Term
  pat-lam   : (cs : list Clause) (args : list (Arg Term)) → Term
  pi        : (a : Arg Term) (b : Abs Term) → Term
  agda-sort : (s : Sort) → Term
  lit       : (l : Literal) → Term
  meta      : (x : Meta) → list (Arg Term) → Term
  unknown   : Term

data Sort where
  set     : (t : Term) → Sort
  lit     : (n : ℕ) → Sort
  prop    : (t : Term) → Sort
  propLit : (n : ℕ) → Sort
  inf     : (n : ℕ) → Sort
  unknown : Sort

data Pattern where
  con    : (c : Name) (ps : list (Arg Pattern)) → Pattern
  dot    : (t : Term)    → Pattern
  var    : (x : ℕ)       → Pattern
  lit    : (l : Literal) → Pattern
  proj   : (f : Name)    → Pattern
  absurd : (x : ℕ)       → Pattern  -- absurd patterns counts as variables

data Clause where
  clause        : (tel : Telescope) (ps : list (Arg Pattern)) (t : Term) → Clause
  absurd-clause : (tel : Telescope) (ps : list (Arg Pattern)) → Clause

{-# BUILTIN AGDATERM      Term    #-}
{-# BUILTIN AGDASORT      Sort    #-}
{-# BUILTIN AGDAPATTERN   Pattern #-}
{-# BUILTIN AGDACLAUSE    Clause  #-}

{-# BUILTIN AGDATERMVAR         var       #-}
{-# BUILTIN AGDATERMCON         con       #-}
{-# BUILTIN AGDATERMDEF         def       #-}
{-# BUILTIN AGDATERMMETA        meta      #-}
{-# BUILTIN AGDATERMLAM         lam       #-}
{-# BUILTIN AGDATERMEXTLAM      pat-lam   #-}
{-# BUILTIN AGDATERMPI          pi        #-}
{-# BUILTIN AGDATERMSORT        agda-sort #-}
{-# BUILTIN AGDATERMLIT         lit       #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown   #-}

{-# BUILTIN AGDASORTSET         set     #-}
{-# BUILTIN AGDASORTLIT         lit     #-}
{-# BUILTIN AGDASORTPROP        prop    #-}
{-# BUILTIN AGDASORTPROPLIT     propLit #-}
{-# BUILTIN AGDASORTINF         inf     #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

{-# BUILTIN AGDAPATCON    con     #-}
{-# BUILTIN AGDAPATDOT    dot     #-}
{-# BUILTIN AGDAPATVAR    var     #-}
{-# BUILTIN AGDAPATLIT    lit     #-}
{-# BUILTIN AGDAPATPROJ   proj    #-}
{-# BUILTIN AGDAPATABSURD absurd  #-}

{-# BUILTIN AGDACLAUSECLAUSE clause        #-}
{-# BUILTIN AGDACLAUSEABSURD absurd-clause #-}
```
