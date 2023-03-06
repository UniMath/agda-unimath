# Library coding style conventions

* This style guide is here to improve the readability of the code. If an item
  in this guide causes suboptimal readability of the code if applied, please
  notify us and we will try to improve this guide, and possibly our code.
* The library uses a standard line length of 80 characters.
* All module headers and standard term definitions should have a single empty line before and after them.
* The library uses Lisp-style parentheses, and indent arguments of functions if they are on their own line.
* The library is universe polymorphic. Whenever a type or type family is assumed, it is assigned its own universe level.

## Names

The naming convention in this library is such that the name of a construction closely matches the type of the construction. For example, the proof that the successor function on the integers is an equivalence has type `is-equiv succ-ℤ`. The name of the proof that the successor function on the integers is an equivalence is therefore `is-equiv-succ-ℤ`. Notice that most names are fully lowercase, and words are separated by hyphens.

Names may also refer to types of the hypotheses used in the construction. Since the first objective of a name is to describe the type of the constructed term, the description of the hypotheses comes after the description of the conclusion in a name. For example, the term `is-equiv-is-contr-map` is a function of type `is-contr-map f → is-equiv f`, where `f` is a function already assumed. This convention has the advantage that if we have `H : is-contr-map f`, then the term `is-equiv-is-contr-map H` contains the description `is-contr-map` closest to the variable `H` of which it is a description.

Our naming conventions are not to ensure the shortest possible names, and neither to ensure the least amount of typing by the implementers of the library, but to display as accurately as possible what concepts are applied, and hence improve the readability.

* We do not use namespace overloading. Unique names should be given to each construction.
* Names should describe in words the concept of its construction.
* As a rule of thumb, names should be entirely lowercase, with words separated by hyphens.
* Names describe the object that is constructed first. For some theorems, the later part of a name contains descriptions of the hypotheses.
* Names never refer to variables.
* Important concepts can be capitalized. Usually, capitalized concepts form categories. Examples include `UU`, `Prop`, `Set`, `Semigroup`, `Monoid`, `Group`, `Preorder`, `Poset`, `Precat`, `Cat`, `Graph`, `Undirected-Graph`.
* The capitalized part of a name only appears at the end of the name.
* Unicode symbols are used sparingly, and only following established mathematical practice.
* Abbreviations are used sparingly, as they also impair the readability of the code.
* If a symbol is not available, the concept is described in words or abbreviated words.
* The readability of the code has high priority. Therefore we try to avoid subtly different variations of the same symbol.
  The only exception to this rule is the use of the [full width equals sign](https://www.fileformat.info/info/unicode/char/ff1d/index.htm) for identity type formation, as the standard equals sign is a reserved symbol in Agda.

## Indentation

* The contents of a top-level module should have zero indentation.
* Every subsequent nested scope should then be indented by an additional two spaces.
* If the variables of a module do not fit on a line, start the variable declarations on a new line, with an indentation of two spaces.
* If the name of a construction does not fit on a single line with its type declaration, then we start the type declaration on a new line, with an indentation of two additional spaces. If the type specification of a construction then still does not fit on a single line of 80 characters, we start new lines in the type declaration using the same indentation level.
* Function arrows at line breaks should always go at the end of the line rather than the beginning of the next line.

## Modules

* As a rule of thumb, there should only be one named module per file. The other modules in the file should be anonymous.
* All module imports should be done directly after the file's named module declaration, and they should be sorted alphabetically.
* Using anonymous modules is encouraged to group constructions by topic, introducing the common arguments of those constructions as parameters. This usually improves the readability of the individual statements as well.
* There should always be a single blank line after a module declaration.
* The variables of a module should be declared on a new line, with a 2-space indentation level. If the variables don't fit on a single line, they can be declared over multiple lines, grouping the variables together logically.
* The `where` keyword is positioned on a new line after the variable declarations, with a 2-space indentation level.

```md
module _
  {l : Level} (G : Group l)
  where
```

## Layout of `where` blocks

* `where` blocks are preferred rather than the `let` construction.
* `where` blocks should be indented by two spaces and their contents should be aligned with the `where`.
* The `where` keyword should be placed on the line below the main proof, indented by two spaces.
* Types should be provided for each of the terms, and all terms should be on lines after the `where`, e.g.

  ```md
  statement : Statement
  statement = proof
    where
    proof : Proof
    proof = some-very-long-proof
  ```

## Functions

* We do not align the arguments or the equality symbol in a function definition.
* If an argument is unused in a function definition, an underscore may be used.
* If a clause of a construction does not fit on the same line as the name and variable declaration, we start the definition on a new line with two spaces of additional indentation

## Types

* Function arguments should be implicit if they can "almost always" be inferred within proofs. It is often harder for Agda to infer an argument in a type declaration, but we prioritize usage in proofs in our decision to make an argument implicit.
* If there are lots of implicit arguments that are common to a collection of proofs they should be extracted by using an anonymous module.
* The library doesn't use variables at the moment. All variables are declared either as parameters of an anonymous module or in the type declaration of a construction.

## Coding practices we avoid

* Unicode characters in names are allowed but use them sparingly. If it is overdone, it will be more difficult to read.
* Names of constructions should never refer to variable names.
* Don't use deeply indented code if a two-space indentation level suffices. Deeply indented code will be rendered unreadable on smaller screens.
* Don't use long lines of code, for the same reason.
* `where` blocks are allowed, but keep them short. Large `where` blocks tend to result in non-reusable and non-refactorable code, and in some instances they slow down Agda's verification process.
* We don't make much use of record types in the `agda-unimath` library. This is because they make it a hassle to characterize their identity type, which is often the first thing we do with a new type. If characterizing the identity type is less relevant, then of course it is convenient to use record types.
* The use of the projection functions `pr1` and `pr2`, and especially their compositions, should be very limited. If a type of the form `Σ A B` is given a name, then it is also worth giving the projections a name. This makes the code more readable, and furthermore if we now jump to the definition of the named projection we will see an informative answer.
* We don't name constructions after infix notation of any operation that occurs in it. Infix notation is always secondary, and in later names that refer to a construction that has infix notation, we refer to the primary prefix notation. For example, the name for the commutativity of cartesian products is `commutative-prod` and not `commutative-×`.
